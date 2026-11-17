#!/usr/bin/perl -w
#
#indx#	remind - Send e-mail reminders based on user's .remind
#@HDR@	$Id$
#@HDR@
#@HDR@	Copyright (c) 2026 Christopher Caldwell (Christopher.M.Caldwell0@gmail.com)
#@HDR@
#@HDR@	Permission is hereby granted, free of charge, to any person
#@HDR@	obtaining a copy of this software and associated documentation
#@HDR@	files (the "Software"), to deal in the Software without
#@HDR@	restriction, including without limitation the rights to use,
#@HDR@	copy, modify, merge, publish, distribute, sublicense, and/or
#@HDR@	sell copies of the Software, and to permit persons to whom
#@HDR@	the Software is furnished to do so, subject to the following
#@HDR@	conditions:
#@HDR@	
#@HDR@	The above copyright notice and this permission notice shall be
#@HDR@	included in all copies or substantial portions of the Software.
#@HDR@	
#@HDR@	THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY
#@HDR@	KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE
#@HDR@	WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE
#@HDR@	AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
#@HDR@	HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
#@HDR@	WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
#@HDR@	FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
#@HDR@	OTHER DEALINGS IN THE SOFTWARE.
#
#hist#	2026-02-09 - Christopher.M.Caldwell0@gmail.com - Created
########################################################################
#doc#	remind - Send e-mail reminders based on user's .remind
#doc#	Invoked once a day in the wee hours of the morning.
########################################################################
#doc##Remind - Software to send e-mail reminders according to dated entries

use strict;
use Date::Manip;

use lib "/usr/local/lib/perl";
use cpi_vars;
use cpi_file qw( fatal echodo read_lines write_lines );
use cpi_arguments qw( parse_arguments );
use cpi_send_file qw( sendmail );
use cpi_time qw( parsedate revlocaltime time_string );
use cpi_translate qw( xprint );
use cpi_cgi qw( CGIreceive CGIheader );
use cpi_user qw( logout_select );
use cpi_setup qw( setup );
use cpi_inlist qw( inlist );

$| = 1;

&setup( stderr=>"Sched" );

# Put constants here

my @MAIL_TYPES = ( "Non recurring", "Recurring" );
my %MAIL_ON_DAYS =
    (
    "Non recurring"	=> [ 0, 1, 2, 7, 14, 30, 60 ],
    "Recurring"		=> [ 0, 1, 2, 7 ]
    );
my $DAY_IN_SECONDS	= ( 60 * 60 * 24 );
#my $FROM		= "reminder\@brightsands.com";
my $FROM		= "chris";

my $SENDMAIL		= "/usr/lib/sendmail";
my $MAIL		= "/usr/bin/Mail";
my $SECONDS_PER_DAY	= 86400;
my $FORM_NAME		= "form";

my $address;
my %entries;
#my ($tsec,$tmin,$thour,$tmday,$tmonth,$tyear,$twday);
my ($tyear,$tmonth,$tmday,$thour,$tmin,$tsec,$twday);
my $UnixDateOffset	= 18000;
my %start_at;
my %stop_at;

our %ONLY_ONE_DEFAULTS =
    (
    "datetime"		=>	time(),
    "file"		=>	"$cpi_vars::BASEDIR/lib/remind.txt",
    "newfile"		=>	"$cpi_vars::BASEDIR/lib/remind.new",
    "mode"		=>	[ "show", "mail", "sort", "html" ],
    "show"		=>	{ "alias"=>["-mode=show"] },
    "mail"		=>	{ "alias"=>["-mode=mail"] },
    "sort"		=>	{ "alias"=>["-mode=sort"] },
    "html"		=>	{ "alias"=>["-mode=html"] },
    "verbosity"		=>	0,
    );

# Put variables here.

our @problems;
our %ARGS;
our @files;
our $exit_stat = 0;
my $record_number = 0;
my @all_records;

my $today;

#########################################################################
#	Print usage message and die.					#
#########################################################################
sub usage
    {
    &fatal( @_, "",
	"Usage:  $cpi_vars::PROG <possible arguments>","",
	"where <possible arguments> is:",
	"    -r <remind file>",
	"    -t <date>",
	"    -d <debug level>"
	);
    }

#########################################################################
#	Return list of entries that match specified date		#
#########################################################################
sub matching_entries
    {
    my( $addr, @params ) = @_;

    my %seen;

    my $must_have = 0;
    foreach my $ind ( "year", "mon", "day" )
        {
	my $val = $params[$must_have];
	grep( $seen{$_->{record}}++,
	    @{$entries{$addr}{$ind}{$val}}, @{$entries{$addr}{$ind}{0}} );
	$must_have++;
	}

    return map {$all_records[$_]} (grep( $seen{$_}==$must_have, keys %seen ));
    }

#########################################################################
#	Return number of seconds since the epoch in year,mon,day	#
#########################################################################
sub epoch_to_ymd
    {
    my($sec,$min,$hr,$day,$mon,$yr,$wd) = localtime($_[0]);
    return ( $yr+1900, $mon+1, $day, $hr, $min, $sec, $wd );
    }

#########################################################################
#	Return pointer to struct with calendar entry			#
#########################################################################
sub make_entry
    {
    my( $address, $yr, $mon, $day, $hhmm, $from_epoch, $every, $rest ) = @_;
    my $ymd = sprintf("%04d-%02d-%02d",$yr,$mon,$day);
    my $whenstr = $ymd
	. ( $every > 0 ? sprintf(":%-3d",$every) : "    " )
	. ( $hhmm ? sprintf(" %s",$hhmm) : "      " );
    #print "cmc whenstr=[$whenstr]\n";
    my $entry =
	{
	"record"	=> $record_number,
	"when"		=> $from_epoch,
	"every"		=> $every,
	"type"		=> ($every?"Recurring":"Non recurring"),
	"whenstr"	=> sprintf("%-20s",$whenstr),
	"hhmm"		=> $hhmm,
	"rest"		=> $rest
	};
    push( @{$entries{$address}{year}{$yr+0}}, $entry );
    push( @{$entries{$address}{mon}{$mon+0}}, $entry );
    push( @{$entries{$address}{day}{$day+0}}, $entry );
    push( @{$entries{$address}{all}}, $entry );
    push( @all_records, $entry );
    $record_number++;
    printf( "%d %s %s %s\n", $entry->{record}, $entry->{whenstr}, $entry, $entry->{rest} )
	if( $ARGS{verbosity} > 1 );
    return $entry;
    }

#########################################################################
#	Read remind file into %entries (and set destination address).	#
#########################################################################
sub read_remind_file
    {
    my @current_entries;
    foreach $_ ( &read_lines( $ARGS{file} ) )
	{
	next if( $_ eq "" );
	my $input = $_;
	if( /^[^\s@]+@[\w\.]+\.\w+$/ )
	    { $address = $_; }
	else
	    {
	    my( $mon, $day, $yr, $every, $rest );
	    if( m~^(\d\d\d\d)-(\d\d*)-(\d\d*):(\d+)\s*(.*?)$~		||
	        m~^(\d\d\d\d|\*)-(\d\d*|\*)-(\d\d*|\*)(\s*)(.*?)$~	)
		{ ($yr,$mon,$day,$every,$rest) = ($1,$2,$3,$4,$5); }
	    elsif(  m~^(\d+)/(\d+)/(\d+):(\d+)\s*(.*)$~		||
		m~^(\d+|\*)/(\d+|\*)/(\d+|\*)(\s+)(.*)$~	)
		{ ($mon,$day,$yr,$every,$rest) = ($1,$2,$3,$4,$5); }
	    if( defined($yr) )
		{
		my $to_print = $input;
		my $hhmm = "";
		$every = ( $every =~ /\d/ ? $every+0 : 0 );

		$yr = 0 if( $yr eq "*" );
		$mon = 0 if( $mon eq "*" );
		$day = 0 if( $day eq "*" );
	        
		if( $rest =~ /^(\d+):(\d+)\s*(.*)/ )
		    {
		    $hhmm = sprintf("%02d:%02d",$1,$2);
		    $rest = $3;
		    }

		$yr += 2000 if( $yr && $yr < 100 );

		my $from_epoch;
		if( grep( ! $_, $yr, $mon, $day ) )
		    { $every = -1; }
		else
		    { $from_epoch = &parsedate("$yr-$mon-$day"); }

		my $entry =
		    &make_entry($address,$yr,$mon,$day,$hhmm,$from_epoch,$every,$rest);
		$entry->{input} = $input;
		@current_entries = ( $entry );

		if( $every >= 0 )	# Not for wildcards
		    {
		    if( $every > 0 )
			{
			my $check_year = $yr + 30;
			my $xind = 0;
			while( $yr < $check_year )
			    {
			    $from_epoch += $DAY_IN_SECONDS * $every;
			    ($yr,$mon,$day) = epoch_to_ymd($from_epoch);
			    my $e =
				&make_entry(
				    $address,$yr,$mon,$day,$hhmm,$from_epoch,$every,$rest);
			    push( @current_entries, $e );
			    $e->{interpolated} = 1;
			    #$e->{input} = (++$xind)."[$input]";
			    }
			}
		    elsif( ! $start_at{$address} )
		        {
			$start_at{$address} = $stop_at{$address}
			    = $from_epoch;
			}
		    elsif( $from_epoch < $start_at{$address} )
		        { $start_at{$address} = $from_epoch; }
		    elsif( $from_epoch > $stop_at{$address} )
		        { $stop_at{$address} = $from_epoch; }
		    }
		}
	    elsif( @current_entries )
		{
		grep( $_->{rest}.=$input, @current_entries );
		}
	    else
		{ print "'$input' not connected to an entry.  Skipping.\n"; }
	    }
	}
    }

#########################################################################
#	Go through entrys hash figuring out e-mail.			#
#########################################################################
sub generate_message
    {
    my( $mode ) = @_;
    #my $now_day = $ARGS{datetime} - ($ARGS{datetime} % $DAY_IN_SECONDS);
    my $now_day = $ARGS{datetime};
    print "generate_message now_day="
        .&time_string("%04d-%02d-%02d %02d:%02d:%02d.%d.\n",$now_day)
	if( $ARGS{verbosity} > 1 );

    my %day_flags;
    foreach my $daytype ( @MAIL_TYPES )
	{ grep( $day_flags{$_}{$daytype}=1, @{$MAIL_ON_DAYS{$daytype}} ); }

    foreach $address ( sort keys %entries )
	{
	my $last_header = "";
	my $txt = "";
	my $found = 0;
	foreach my $entry_type ( @MAIL_TYPES )
	    {
	    foreach my $offset ( @{$MAIL_ON_DAYS{$entry_type}} )
		{
		#$txt .= "Looking at offset=$offset entry_type=$entry_type\n";
		my $hdr = "\n$entry_type events " .
		    ( $offset <= 0 ? "today"
		    : $offset <= 1 ? "tomorrow"
		    : "in $offset days" ) . ":\n";
		my( $cyear, $cmonth, $cmday ) =
		    &epoch_to_ymd($now_day + $offset*$DAY_IN_SECONDS);
		#$txt .= sprintf( "CMC ymd=%04d-%02d-%02d\n",$cyear,$cmonth,$cmday);
		foreach my $entry (
		    sort {$a->{hhmm} cmp $b->{hhmm}}
		    &matching_entries($address,$cyear,$cmonth,$cmday) )
		    {
		    if( $entry_type eq $entry->{type} )
			{
			if( $hdr ne $last_header )
			    {
			    $txt .= $hdr;
			    $last_header = $hdr;
			    }
    #		    $txt .= sprintf("%d-%02d:%02d:%02d %s",
    #			$diff/$DAY_IN_SECONDS,
    #			($diff % $DAY_IN_SECONDS) / 3600,
    #			($diff % 3600) / 60,
    #			($diff %60),
			#print "entry=[$entry]\n";
			#print "whenstr=[",$entry->{whenstr},"]\n";
			$txt .= sprintf(" %s %s\n",$entry->{whenstr}, $entry->{rest});
			#$txt .= "\n" . $entry->{record} . ":" . $entry->{every} . ":" . $entry->{input} . "\n";
			$found++;
			}
		    }
		}
	    }

	my $subject =
	    ( $found<=0 ?	"NO reminders for $today"
	    : $found==1 ?	"$found reminder for $today"
	    :			"$found reminders to $today" );

	if( $mode eq "show" )
	    {
	    print "Debug Mail -s '$subject' $address\n",
	        ( $txt ? $txt : "$subject\n" );
	    }
	elsif( $mode eq "mail" )
	    {
	    &sendmail( $FROM, $address, $subject, $txt );
	    }
	elsif( $MAIL )
	    {
	    #print "Mail subject=[$subject] address=[$address]\n";
	    open(OUT, "|Mail -s '$subject' $address")
		|| die("Cannot run ${MAIL}:  $!");
	    print OUT ( $txt ? $txt : "$subject\n" );
	    close( OUT );
	    }
	elsif( $SENDMAIL )
	    {
	    #print "Sendmail logic.\n";
	    if( $FROM )
		{
		open(OUT, "| $SENDMAIL -t -f $FROM" )
		    || die("Cannot run ${SENDMAIL}:  $!");
		}
	    else
		{
		open(OUT, "| $SENDMAIL -t" )
		    || die("Cannot run ${SENDMAIL}:  $!");
		}
	    print OUT <<MAILEOF;
To:  $address
Subject:  $subject

$txt
MAILEOF
	    close(OUT);
	    }
	}
    }

#########################################################################
#	Read file in and sort it.					#
#########################################################################
sub do_sort
    {
    my @toprint;
    foreach $address ( sort keys %entries )
        {
	push( @toprint, $address );
	foreach my $ep ( sort { $a->{whenstr} cmp $b->{whenstr} }
	    grep( ! $_->{interpolated}, @{$entries{$address}{all}} ) )
	    {
	    push( @toprint, $ep->{whenstr} . " " . $ep->{rest} );
	    }
	}

    &write_lines( $ARGS{newfile}, @toprint );

    print "size of $ARGS{file} = ", -s $ARGS{file}, ".\n";
    print "size of $ARGS{newfile} = ", -s $ARGS{newfile}, ".\n";
    &fatal("Sorting from $ARGS{newfile} to $ARGS{file} caused a corruption.")
        if( -s $ARGS{file} != -s $ARGS{newfile} );
    #&echodo("cat '$ARGS{newfile}' > '$ARGS{file}' && rm -f '$ARGS{newfile}'");
    }

#########################################################################
#	Display the items found by a search.				#
#########################################################################
sub setup_time_report()
    {
    my $earliest;
    my $latest = 0;
    foreach my $key ( @_ )
        {
	my $startdt = &DBFcache($key,"Started_working");
	if( $startdt =~ m=(\d+/\d+/\d+)= )
	    {
	    my $ind	= $1;
	    my $start	= &parsedate($startdt);
	    my $stop	= &parsedate(&DBFcache($key,"Stopped_working"));
	    $earliest = $start if( !defined($earliest) || $start < $earliest );
	    $latest = $stop if( $stop > $latest );
	    #$key_starts{$key} = $start;
	    #$key_times{$key} = $stop - $start;
	    #push( @{$keys_on_day{$ind}}, $key );
	    }
	}
#    $earliest = &parsedate($constraints{$thisrep}{"Search_from"})
#	if( $constraints{$thisrep}{"Search_from"} );
#    $latest = &parsedate($constraints{$thisrep}{"Search_to"})
#	if( $constraints{$thisrep}{"Search_to"} );
    return ( $earliest, $latest )
    }

#########################################################################
#	Print a calendar						#
#########################################################################
sub calendar
    {
    my( $need_header, $fieldp, @klist ) = @_;
    my $here = $cpi_vars::FORM{here};

    &setup_time_report(@klist);
    #my( $start_at, $stop_at ) = &setup_time_report(@klist);

    my @toprint = ( "<input type=hidden name=key><table border=1><tr>",
        join( "", map { "<th>XL(${_}day)</th>" }
	    ("Sun","Mon","Tues","Wednes","Thurs","Fri","Satur") ) );
    
    my $now = time();
    my($tyear,$tmonth,$tmday) = &epoch_to_ymd($now);

    foreach $address ( sort keys %entries )
	{
	my($cyear,$cmonth,$cmday,$chour,$cmin,$csec,$wday)
	    = ( $tyear, $tmonth, $tmday, $thour, $tmin, $tmday );
	    #= epoch_to_ymd($start_at{$address});
#	printf("ymd($start_at{$address}}=%04d-%02d-%02d %02d:%02d:%02d %d.\n",
#	    $cyear, $cmonth, $cmday, $chour, $cmin, $csec, $wday );
	my $firstmonth = &revlocaltime($csec,$cmin,$chour,1,$cmonth-1,$cyear-1900);
	($cyear,$cmonth,$cmday,$chour,$cmin,$csec,$wday)
	    = epoch_to_ymd($firstmonth);
#	printf("fm($firstmonth)=%04d-%02d-%02d %02d:%02d:%02d %d.\n",
#	    $cyear, $cmonth, $cmday, $chour, $cmin, $csec, $wday );
	my $timeind = $firstmonth - $SECONDS_PER_DAY*$wday;
	($cyear,$cmonth,$cmday,$chour,$cmin,$csec,$wday) = &epoch_to_ymd($timeind);
#	printf("week($timeind)=%04d-%02d-%02d(%d).\n",$cyear,$cmonth,$cmday,$wday);

	my $check_year;
	my $check_month;
	my $col;
	$here=sprintf("%04d-%02d-%02d",$tyear,$tmonth+1,$tmday)
	    if( ! $here );
	do  {
	    push( @toprint, "</tr>\n<tr>" ) if( $wday==0 );
	    #push( @toprint, "<td>[".($wday||0).",".($check_year||"UNDEF")."]</td>");
	    my $green = 0xa0 + ($cmonth % 3) * 0x10;
	    my $is_today = ($cyear==$tyear && $cmonth==$tmonth && $cmday==$tmday);

	    if( $is_today )
		{ $col = sprintf("#%02x%02x%02x",0xff,$green,0xb0); }
	    elsif( $timeind < $now )
		{ $col = sprintf("#%02x%02x%02x",0xb0,$green,0xb0); }
	    else
		{ $col = sprintf("#%02x%02x%02x",0xc0,$green,0xff); }
		
	    my $datetext = sprintf("%04d-%02d-%02d",$cyear,$cmonth,$cmday);
	    push( @toprint, "<td bgcolor='$col' valign=top><b>",
		"<a",
		( $here && $here eq $datetext ? " name=here" : "" ),
		" href='javascript:get_an_entry(\"$datetext\");'>" );
	    push( @toprint,
		( defined($check_month) && $cmonth==$check_month && $cyear==$check_year )
		? sprintf("%02d",$cmday)
		#? sprintf("%02d(%04d-%02d)",$cmday,$check_year,$check_month)
		: $datetext );
	    push( @toprint, "</a></b>" );
	    if( my @entries_today =
		&matching_entries($address,$cyear,$cmonth,$cmday) )
		{
		foreach my $entry (
		    sort {$a->{hhmm} cmp $b->{hhmm}} @entries_today )
		    {
		    my $text = "something";
		    push( @toprint, "<br>",
			( $entry->{hhmm} ? $entry->{hhmm}." " : "* " ),
			"<a href='javascript:window.document.$FORM_NAME.key.value",
			"=$text;window.document.$FORM_NAME.submit();'>",
			$entry->{rest},
			"</a>" );
		    }
		}
	    push( @toprint, "</td>" );
	    $timeind += $SECONDS_PER_DAY;
	    $check_year = $cyear;
	    $check_month = $cmonth;
	    ($cyear,$cmonth,$cmday,$chour,$cmin,$csec,$wday)
		= &epoch_to_ymd($timeind);
	    } while( $timeind<=$stop_at{$address} || $cmonth==$check_month );
	}
    push( @toprint, "</tr></table>\n" );
    print STDERR "Returning [",@toprint,"]\n";
    return join("",@toprint);
    }

#########################################################################
#	Print footer (dependent on privileges).				#
#########################################################################
sub footer()
    {
    my( $mode ) = @_;
    $mode ||= "admin";

    my $href = "$cpi_vars::THIS?SID=$cpi_vars::SID&USER=$cpi_vars::USER";
    my $c = "#d0e0ff";
    my @toprint = ( "<p><center><table width=60% border=4><tr>" );
    my @buttons;
    foreach my $button ( @buttons )
        {
	my( $butdest, $buttext ) = split(/:/,$button);
	push( @toprint, "<th><input type=button help='button_$butdest' onClick='window.location=\"$href&func=$butdest\";'",
	    ( ($butdest eq $mode) ? " style='background-color:cyan'" : "" ),
	    " value=\"$buttext\"></th>" );
	}
    push( @toprint, "<th><input type=button help='Help' value=\"XL(Help)\" ");
    push( @toprint, "onClick='open(\"$href&func=help\",\"help\",\"toolbar=0,location=0,directories=0,status=0,menubar=0\");'></th>");
    push( @toprint, "<th>", &logout_select(), "</th>");
    push( @toprint, "</tr></table></center>");
    &xprint( @toprint );
    &cleanup(0);
    }

#########################################################################
#	Show the primary screen.					#
#########################################################################
sub userpage_handler
    {
    if( $cpi_vars::FORM{new_entry} && $cpi_vars::FORM{here} )
        {
	open( REM, ">> $ARGS{file}" ) ||
	    &fatal("Cannot append to $ARGS{file}:  $!");
	print REM $cpi_vars::FORM{here}, " ", $cpi_vars::FORM{new_entry}, "\n";
	close( REM );
	}

    my $toprint = <<EOF . &calendar() . "</center>";
<script>

//////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////
function get_an_entry( datestr )
    {
    with ( window.document )
        {
	$FORM_NAME.new_entry.value
	    = prompt("XL(Enter hh:mm entry for) "+datestr);
	$FORM_NAME.here.value = datestr;
	$FORM_NAME.submit();
	}
    }
</script>

</head><body $cpi_vars::BODY_TAGS>
$cpi_vars::HELP_IFRAME
<form name=$FORM_NAME method=post>
<input type=hidden name=SID value=$cpi_vars::FORM{SID}>
<input type=hidden name=USER value=$cpi_vars::USER>
<input type=hidden name=func value=Update>
<input type=hidden name=here>
<input type=hidden name=new_entry>
<center>
EOF
    &xprint( $toprint );
    &footer();
    &cleanup(0);
    }

##########################################################################
##	Do substitutions in a javascript template file.			#
##########################################################################
#sub template_substitutions
#    {
#    my( $fn, @varvals ) = @_;
#    my $text = &read_file( $fn );
#    push( @varvals,
#	"BODY_TAGS",	$cpi_vars::BODY_TAGS,
#	"TABLE_TAGS",	$cpi_vars::TABLE_TAGS,
#	"SID",		$cpi_vars::SID,
#	"USER",		$cpi_vars::USER,
#	"SEPS",		join(",", map { "${_}:'$SEP{$_}'" } keys %SEP )
#	);
#    grep( $text =~ s/\b${_}_SEP\b/'$SEP{$_}'/gs, keys %SEP );
#    while( my $tvar = shift(@varvals) )
#        {
#	my $tval = shift(@varvals);
#	$text =~ s/%%${tvar}%%/$tval/gs;
#	}
#    return $text;
#    }

#########################################################################
#########################################################################
sub CGI_arguments
    {
    &CGIreceive();
    &parse_arguments();
    }

#########################################################################
#	Main								#
#########################################################################

if( $ENV{SCRIPT_NAME} )
    { &CGI_arguments(); }
else
    { &parse_arguments(); }

$ARGS{datetime} = &parsedate($ARGS{datetime}) if( $ARGS{datetime} !~ /^\d+$/ );

$today = localtime( $ARGS{datetime} );
print "localtime=[$today]\n" if( $ARGS{verbosity} );
$today =~ s/ \d\d:\d\d:\d\d//;
$today =~ s/\s+/ /g;
$today =~ s/( \d\d\d\d)/,$1/;
#($tsec,$tmin,$thour,$tmday,$tmonth,$tyear,$twday) = localtime($ARGS{datetime});
($tyear,$tmonth,$tmday,$thour,$tmin,$tsec,$twday) = &epoch_to_ymd($ARGS{datetime});
$today = sprintf("%04d-%02d-%02d",$tyear,$tmonth,$tmday);
print "today=[$today]\n" if( $ARGS{verbosity} );

&read_remind_file();

if( $ENV{SCRIPT_NAME} || $ARGS{mode} eq "html" )
    { &userpage_handler(); }
elsif( $ARGS{mode} eq "sort" )
    { &do_sort(); }
elsif( &inlist($ARGS{mode},"mail","show") )
    { &generate_message( $ARGS{mode} ); }

exit($exit_stat);
