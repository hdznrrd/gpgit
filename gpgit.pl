#!/usr/bin/perl

##############################################################################
#                                                                            #
# Copyright 2011, Mike Cardwell - https://grepular.com/                      #
# Automatic extraction of recipients 2014, Gregor Jehle                      #
#                                                                            #
# This program is free software; you can redistribute it and/or modify       #
# it under the terms of the GNU General Public License as published by       #
# the Free Software Foundation; either version 2 of the License, or          #
# any later version.                                                         #
#                                                                            #
# This program is distributed in the hope that it will be useful,            #
# but WITHOUT ANY WARRANTY; without even the implied warranty of             #
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the              #
# GNU General Public License for more details.                               #
#                                                                            #
# You should have received a copy of the GNU General Public License          #
# along with this program; if not, write to the Free Software                #
# Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA #
#                                                                            #
##############################################################################

use strict;
use warnings;
use Mail::GnuPG;
use MIME::Parser;
use Mail::Header;
use Mail::Field;
use Data::Dumper;
use Time::HiRes;
use Mail::Box::Manager;
use Mail::Box::Message;
use File::Temp;

my $fail_if_already_encrypted = 1;
my $logging_enabled = 1;
my $debug_dump_each_mail = 1;

## Parse args
my $encrypt_mode   	= 'pgpmime';
my $inline_flatten 	= 0;
my @recipients     	= ();
my $gpg_home       	= 0;
my %gpg_params 		= ();
my $dump_fails_to_mbox	= 1;
my $sysadmin_email	= "";
my $notification_email_template_file = "";
my $sanitize_extension_headers	= 0;

my $fail_mbox_file		= "/var/log/exim4/failure.mbox";
my $email_dump_mbox_file 	= "/var/log/exim4/dump.mbox";
my $debug_logfile_name 		= "/var/log/exim4/cryptowrapper.debug.log";

my $debug_no_send_mail	= 0;

my $email_from = "";

my $reference		= &generateReference();

{
	my @args = @ARGV;
     	while( @args ) {
        	my $key = shift @args;
    		if( $key eq '--help' || $key eq '-h' ) {
			help();
		}
		elsif( $key eq '--encrypt-mode' )		{ $encrypt_mode = shift @args;
							  	  unless( defined $encrypt_mode
								  	  && grep( $encrypt_mode eq $_, 'prefer-inline', 'pgpmime', 'inline-or-plain' ) )
									  { die "Bad value for --encrypt-mode\n"; }
		}
		elsif( $key eq '--gpg-home' ) 			{ $gpg_params{'keydir'} = shift @args; }
		elsif( $key eq '--gpg-path' )			{ $gpg_params{'gpg_path'} = shift @args; }
		elsif( $key eq '--always-trust' )		{ $gpg_params{'always_trust'} = 1; }
		elsif( $key eq '--inline-flatten' )		{ $inline_flatten = 1; }
		elsif( $key eq '--failure-mbox-file' )		{ $dump_fails_to_mbox = 1; $fail_mbox_file = shift @args; }
		elsif( $key eq '--sysadmin-email')		{ $sysadmin_email = shift @args; }
		elsif( $key eq '--notification-email-template') { $notification_email_template_file = shift @args; }
		elsif( $key eq '--debug-logfile') 		{ $debug_logfile_name = shift @args; }
		elsif( $key eq '--email-dump-mbox-file')	{ $email_dump_mbox_file = shift @args; }
		elsif( $key eq '--sanitize-extension-headers')	{ $sanitize_extension_headers = 1; }
		elsif( $key eq '--debug-no-send-mail')		{ $debug_no_send_mail = 1; }
		elsif( $key eq '--from')			{ $email_from = shift @args; }
		elsif( $key =~ /^.+\@.+$/ )			{ push @recipients, $key; }
		else {
			die "Bad argument: $key\n";
		}
	}
	if( $inline_flatten && $encrypt_mode eq 'pgpmime' ){
        	die "inline-flatten option makes no sense with \"pgpmime\" encrypt-mode. See --help\n"
	}
}

# Basic LANGSEC
&lsEnsureWritableFileOrDoesNotExist($fail_mbox_file);
&lsEnsureWritableFileOrDoesNotExist($debug_logfile_name) if($logging_enabled);
&lsEnsureWritableFileOrDoesNotExist($email_dump_mbox_file) if($debug_dump_each_mail);
&lsEnsureValidEmailAddress($sysadmin_email) if(defined $sysadmin_email);
&lsEnsureReadableFile($notification_email_template_file) if(defined $notification_email_template_file);
&lsEnsureValidEmailAddress($email_from);
&lsEnsurePopulatedArray(\@recipients);
map { &lsEnsureValidEmailAddress($_) } @recipients;





## Set the home environment variable from the user running the script
$ENV{HOME} = (getpwuid($>))[7];

## Read the plain text email
my $plain = "";
{
	local $/=undef;
	$plain = <STDIN>;
}

## some global variables used to build error report mails
#
# just the email headers as string blob
my $header = "";

# a string comprised of the destination addressees of the mail
my $destinations = "";

# a string containing the sender address
my $origin = $email_from;


&log("INFO: processing mail");

if($sanitize_extension_headers) {
	&log("DEBUG: Sanitizing extension headers");
	# matches any X-headers including the rest of the line
	#   as well as the newline character.
	# if the next line starts with whitespace + non-whitespace combo
	# we're dealing with a line-broken long header entry.
	# we're removing those as well.
	$plain =~ s/^X\-.+?(\n\s\S.+?)*\n(?!\s\S)//mg;
}

# dump the mail before we do anything to it.
&writeToMbox($email_dump_mbox_file, $plain) if($debug_dump_each_mail);

# we might have to send the admin an error report.
# for this we want to include headers.
$header = &extractHeaders($plain);

$destinations = join(', ', @recipients);

if(scalar @recipients == 0) {
	&sendErrorMailAndLog("ERROR: no receipients known for email.");
	&writeToMbox($fail_mbox_file, $plain) if($dump_fails_to_mbox);
	print &generateWarningMail();
        exit 1;
}

&log("INFO: proceeding to encrypt mail to: ".join(", ", @recipients));

## Object for GPG encryption
my $gpg = new Mail::GnuPG(%gpg_params);

## Make sure we have the appropriate public key for all recipients
foreach( @recipients ){
     my $target = $_;
     unless( $gpg->has_public_key( $target ) ){
	&sendErrorMailAndLog("ERROR: missing key for $target. Not sending email.");
	&writeToMbox($fail_mbox_file, $plain) if($dump_fails_to_mbox);
	print &generateWarningMail();
        #while(<STDIN>){
           #print;
        #}
        exit 1;
     }
}

## Parse the email
my $mime;
{
     my $parser = new MIME::Parser();
     $parser->decode_bodies(1);
     $parser->output_to_core(1);
     $mime = $parser->parse_data( $plain );
}

## Test if it is already encrypted
  if( $gpg->is_encrypted( $mime ) ){
	if($fail_if_already_encrypted) {
     		&sendErrorMailAndLog("ERROR: email is already encrypted. This should not happen");
	} else {
     		&log("INFO: mail is already encrypted");
     		print $plain;
	}
     exit 1;
  }

## If the user has specified that they prefer/need inline encryption, instead of PGP/MIME, and the email is multipart, then
## we need to attempt to flatten the message down into a single text/plain part. There are a couple of safe'ish lossy ways of
## doing this:
##
## Removing text/html from multipart/alternative entities that also have a text/plain part
##   In this scenario, the two text parts are *supposed* to contain the same content. So it should be ok to strip the html part.
##   We only do this if the text/plain part contains at least 10 characters of data.
##
## Removing images from multipart/related entities when they are referred to from a HTML part
##   We'll be stripping the HTML parts, so if those HTML parts use a CID URL to refer to a related image, we may as well strip
##   those images too as they will no longer be used in the display of the email

  if( $inline_flatten ){
     if( $encrypt_mode eq 'prefer-inline' || $encrypt_mode eq 'inline-or-plain' ){
        if( $mime->mime_type =~ /^multipart\/(alternative|related)$/ ){

           ## We're going to try several things to flatten the email to a single text/plain part. We want to work on a duplicate
       ## version of the message so we can fall back to the original if we don't manage to flatten all the way
             my $new_mime = $mime->dup;

           ## Remember the original MIME structure so we can add it to an information header
             my $orig_mime_structure = mime_structure( $mime );

       ## We may already be able to safely flatten, if we have a multipart/x message with only a single child part. Unlikely
             $new_mime->make_singlepart;

           ## multipart/related
             flatten_related( $new_mime     ) if $new_mime->mime_type eq 'multipart/related';
             flatten_alternative( $new_mime ) if $new_mime->mime_type eq 'multipart/alternative';

           ## Keep the new message if it was succesfully flattened
             if( $new_mime->mime_type !~ /^multipart\// ){
                $new_mime->head->add('X-GPGIT-Flattened-From', $orig_mime_structure );
                $mime = $new_mime;
             }
        }
     }
  }

## Encrypt
  {
     my $code;
     if( $encrypt_mode eq 'pgpmime' ){
        $code = $gpg->mime_encrypt( $mime, @recipients );
     } elsif( $encrypt_mode eq 'prefer-inline' ){
        $mime->make_singlepart;
        $code = $mime->mime_type =~ /^text\/plain/
              ? $gpg->ascii_encrypt( $mime, @recipients )
              : $gpg->mime_encrypt(  $mime, @recipients );
     } elsif( $encrypt_mode eq 'inline-or-plain' ){
        $mime->make_singlepart;
        if( $mime->mime_type =~ /^text\/plain/ ){
       $code = $gpg->ascii_encrypt( $mime, @recipients );
    } else {
	&sendErrorMailAndLog("ERROR: encryption mode failure: \"$encrypt_mode\". Not sending email.");
	&writeToMbox($fail_mbox_file, $plain) if($dump_fails_to_mbox);
	print &generateWarningMail();
        exit 1;
    }
     }

     if( $code ){
	&sendErrorMailAndLog("ERROR: key error $code for $destinations. Maybe an expired key? Not sending email.");
	&writeToMbox($fail_mbox_file, $plain) if($dump_fails_to_mbox);
	print &generateWarningMail();
    exit 1;
     }
  }

## Remove some headers which might have been broken by the process of encryption
  $mime->head()->delete($_) foreach qw( DKIM-Signature DomainKey-Signature );

## Print out the encrypted version
  print $mime->stringify;

## Flatten multipart/alternative by removing html parts when safe
  sub flatten_alternative {
     my $entity = shift;

     my @parts = $entity->parts;

     if( int(@parts) == 2 && $parts[0]->mime_type eq 'text/plain' && $parts[1]->mime_type eq 'text/html' ){
        my $body = $parts[0]->bodyhandle->as_string;
        $body =~ s/^[\s\r\n]*(.*?)[\s\r\n]*$/$1/s;
        if( length($body) >= 10 ){
           $entity->parts([$parts[0]]);
           $entity->make_singlepart;
        }
     }
  }

## Flatten multipart/related by removing images when safe
  sub flatten_related {
     my $entity = shift;

     ## Scan the existing parts
       my( @parts, %cids );
       foreach my $part ( $entity->parts ){
          if( $part->mime_type =~ /^image\// ){
             my $content_id = $part->head->get('Content-Id')||'';
             $content_id =~ s/^<(.+?)>$/$1/;
             $content_id =~ s/[\r\n]+//g;
             if( length($content_id) ){
                push @parts, { content_id => $content_id, part => $part };
                next;
             }
          } elsif( $part->mime_type eq 'text/html' ){
             $cids{$_} = 1 foreach get_cids_from_html( $part );
          } elsif( $part->mime_type eq 'multipart/alternative' ){
             foreach my $part ( grep( $_->mime_type eq 'text/html', $part->parts ) ){
                $cids{$_} = 1 foreach get_cids_from_html( $part );
             }
          }
          push @parts, { part => $part };
       }

     ## Remove images linked to from HTML
       my @new_parts;
       foreach my $part ( @parts ){
          next if exists $part->{content_id} && $cids{$part->{content_id}};
          push @new_parts, $part->{part};
       }

     ## If we've managed to get rid of at least one child part, then update the mime entity
       if( int(@new_parts) < int(@parts) ){
          $entity->parts(\@new_parts);
          $entity->make_singlepart();
       }
}

## Takes a HTML part, and looks for CID urls
  sub get_cids_from_html {
     my $entity = shift;

     ## Get the decoded HTML
       my $html = $entity->bodyhandle->as_string;

     ## Replace newlines with spaces
       $html =~ s/\s*[\r\n]+\s*/ /gsm;

     ## Parse out cid urls
       my @cids;
       $html =~ s/=\s*["']?cid:(.+?)["'\s\/>]/push @cids,$1/egoism;

     return @cids;
  }

  sub mime_structure {
     my $entity = shift;
     if( $entity->mime_type =~ /^multipart\/.+/ ){
        my @parts = $entity->parts;
    return $entity->mime_type.'('.join(",",map {mime_structure($_)} @parts).')';
     } else {
        return $entity->mime_type;
     }
  }

## generate a logging timestamp
# returns: timestamp (string)
sub getLoggingTime {
    my ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst)=localtime(time);
    my $nice_timestamp = sprintf ( "%04d-%02d-%02d %02d:%02d:%02d",
                                   $year+1900,$mon+1,$mday,$hour,$min,$sec);
    return $nice_timestamp;
}

## Log a single line
sub log {
	if($logging_enabled) {
		my $msg = shift;
     		print &getLoggingTime(), " - ", $reference , " - ", $msg, "$/";
        	open(my $fh, ">>", "$debug_logfile_name");
        	print $fh &getLoggingTime(), " - ", $msg, "$/";
        	close($fh);
	}
}

## log a mail by appending it to an mbox file
sub writeToMbox {
	my $mbox_file_name = shift;
	my $content = shift;
	
	# prepend our own reference
	$content = "X-Cryptowrapper-Reference: $reference\r\n".$content;

	# now parse it into a message
	my $mail = Mail::Box::Message->read($content);

	# open the mbox file (or create it)
	my $mgr = new Mail::Box::Manager;
	my $folder = $mgr->open(folder => "$mbox_file_name",
				create => 1,
				type => 'Mail::Box::Mbox',
				access => 'rw');

	# off we go
	$folder->addMessage($mail);

	$folder->close();
}

sub generateReference {
	my $tmp = mktemp("XXXXXXXX");
	my $ts = &getLoggingTime();
	$ts =~ s/[\s\:\-]//g;
	return "${ts}_${tmp}";
}

## sanitize a mail by removing sensitive content
sub generateWarningMail {
	return <<EOM
From: "Cryptowrapper <$sysadmin_email>"
Subject: WARNING: Encryption failure notification


You're receiving this mail because "$origin" wanted to
send you an email but I was not able to encrypt it.

Reference: $reference

Best regards,
Cryptowrapper


EOM
}

## extracts all header lines from a mail
# param: mail (array of strings, one line per entry)
# returns: headers (single string)
sub extractHeaders {
	my @mail = split /\r?\n/, shift;
	my $header = "";
        while(my $line = shift @mail) {
                chomp($line);
                chomp($line);
 
                # did we reach the newline separating header from body?
                last if(length($line) == 0);
 
                $header .= $line."\r\n";
        }
        return $header;
}

## fetches global variables to build and send an admin notification mail
# param: error message (string)
sub sendErrorMailAndLog {
	my $errormsg = shift;
	&log($errormsg);
	&sendAdminNotificationMail($sysadmin_email, $notification_email_template_file, $errormsg, $origin, $destinations, $header);
}

## generates an admin notification mail and tries to send it to the admin address
# param: sysadmin email address (string or number 0 if no mail should be sent)
# param: template filename (string)
# param: error message (string)
# param: sender address (string)
# param: destination addresses (string)
# param: headers of original email (string)
sub sendAdminNotificationMail {
	my $sysadminaddress = shift @_;

	return if(!$sysadminaddress);

	if($debug_no_send_mail) {
		print "PIPECOMMAND: |mail -s \"Failed to encrypt outgoing email\" $sysadminaddress\n";
		print &buildAdminNotificationMailBody(@_);
	} else {
		open(my $pipe, "|mail -s \"Failed to encrypt outgoing email\" $sysadminaddress");
		if(!$pipe) {
			&log("ERROR: failed to open pipe to 'mail': $!");
		} else {
			print $pipe &buildAdminNotificationMailBody(@_);
			close($pipe);
		}
	}
}

## builds the mail body of an admin notification mail
# param: template filename (string)
# param: error message (string)
# param: sender address (string)
# param: destination addresses (string)
# param: headers of original email (string)
sub buildAdminNotificationMailBody {
	my ($tplfile, $errormessage, $origin, $destinations, $header) = @_;

	my $tpl = "";
	open(my $fh, "<", $tplfile) or return "Cryptowrapper wanted to send you an email, letting you\r\nknow that encryption of an outgoing email failed.\r\nHowever, Cryptowrapper failed to open the template \"$tplfile\": $!\r\n\r\n";
	while(<$fh>) {
		$tpl .= $_;
	}

	$tpl =~ s/{{errormessage}}/$errormessage/g;
	$tpl =~ s/{{destinations}}/$destinations/g;
	$tpl =~ s/{{origin}}/$origin/g;

	$tpl =~ s/{{reference}}/$reference/g;

	$header = "> ".join("\r\n> ",split /\r?\n/, $header);

	$tpl =~ s/{{header}}/$header/g;

	return "$tpl\r\n";
}


## parses an array of config lines into a hash lookup table
# param: config file contents (array of strings in format "from: to1, to2, to3, ...")
# returns: lookup table (hash ref, key: string, value: ref(array of strings))
sub rw_parse_config()
{
	my %conf = ();
	while(my $entry = shift)
	{
		my ($from, $to) = split(/\s*:\s*/, $entry);
		$conf{lc($from)} = [map { lc($_) } split(/\s*,\s*/, $to)];
	}
	return \%conf;
}

## reads contents of configuration file
# param: configuration filename (string)
# returns: file contents (array of strings)
sub rw_read_config()
{
	my $fname = shift;
	my @lines = ();
	open(my $fh, "<", $fname) or return @lines;
	while(my $line = <$fh>)
	{
		chomp($line);
		push @lines, $line;
	}
	return @lines;
}

# checks equality of two arrays by value
# param: first array ref(array of string)
# param: second array ref(array of string)
# return: 1 or 0
sub is_address_array_effectively_the_same()
{
	my $la = shift;
	my $lb = shift;
	my %ha = map { $_ => 1 } @{$la};
	
	foreach(@{$lb})
	{
		return 0 if(!exists $ha{$_});
	}
	return 1;
}


sub help {
   print << "END_HELP";
Usage: gpgit.pl [recipient ...]

Gpgit takes an optional list of email addresses as its arguments. The email
is encrypted using the public keys associated with those email addresses as
well as those found in To:, Cc:, Bcc: fields. Those public keys
*MUST* have been assigned "Ultimate" trust or it wont work.

Optional arguments:

  --help or -h

Display this usage information.

  --gpg-home /path/to/gpg/config/

Set the location of the GnuPG configuration and keyring

  --always-trust

Trust all keys, even if trust level is not 'Ultimate'

  --encrypt-mode prefer-inline / pgpmime / inline-or-plain

Single part text emails can be encrypted inline, or using PGP/MIME. Multi-part
emails can only be encrypted using PGP/MIME. "pgpmime" is the default for this
argument and means we will always use PGP/MIME. "prefer-inline" means that we
will use inline if possible, and PGP/MIME if not. "inline-or-plain" will use
inline encryption for single part emails, and no encryption for multi-part
emails.

  --inline-flatten

Only makes sense when using an "inline" encrypt-mode. When you enable this
option, we attempt to convert multipart emails to a single part text/plain
email, so inline encryption can be used. The methods we use are "lossy", but
I believe them to be safe(ish):

1.) When we find a multipart/alternative part which contains two parts: A
    text/plain part with at least 10 characters in it, and a text/html part,
    we remove the text/html part. The text/plain part *should* contain the
    same content as the text/html part, but without the HTML markup.

2.) When we find a multipart/related part which contains image parts which
    are referred to from a HTML part via CID URLs, we remove those images.
    We can do this, because we will be removing the HTML parts that are
    referring to them, and so they *should* be redundant. We don't just
    remove image parts, we only remove "related" image parts that are
    referred by using CID URLs pointing at their Content-Id headers.
END_HELP
  exit 0;
}

# some simple LANGSEC tests
sub lsEnsurePopulatedArray {
	my $candidate = shift;
	if(scalar @{$candidate} == 0) {
		&log("ERROR: lsEnsurePopulatedArray failed on \"$candidate\"");
		die;
	}
	return $candidate;
}

sub lsEnsureExecutable {
	my $candidate = shift;
	if(!-x $candidate or !-r $candidate) {
		&log("ERROR: lsEnsureExecutable failed on \"$candidate\"");
		die;
	}
	return $candidate;
}

sub lsEnsureReadablePath {
	my $candidate = shift;
	if(!-d $candidate) {
		&log("ERROR: lsEnsureReadablePath failed on \"$candidate\"");
		die;
	}
	&lsEnsureExecutable($candidate);
	return $candidate;
}

sub lsEnsureWritableFileOrDoesNotExist {
	my $candidate = shift;
	if(-e $candidate and !-w $candidate) {
		&log("ERROR: lsEnsureWritableFileOrDoesNotExist failed on \"$candidate\"");
		die;
	}
	return $candidate;
}

sub lsEnsureReadableFile {
	my $candidate = shift;
	if(!-r $candidate) {
		&log("ERROR: lsEnsureReadableFile failed on \"$candidate\"");
		die;
	}
	return $candidate;
}

sub lsEnsureValidEmailAddress {
	my $candidate = shift;
	if ($candidate !~ /^[a-z0-9\!\#\$\%\&\'*+\/\=\?\^_\`\{\|\}\~\-]+(?:\.[a-z0-9!#\$\%\&\'\*\+\/\=\?\^_\`\{\|\}\~\-]+)*\@(?:[a-z0-9](?:[a-z0-9-]*[a-z0-9])?\.)*?[a-z0-9](?:[a-z0-9-]*[a-z0-9])?$/) {
		&log("ERROR: lsEnsureValidEmailAddress \"$candidate\"");
		die;
	}
	return $candidate;
}
