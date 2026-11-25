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
#doc#	Web allows you to review and update schedule.
########################################################################

use strict;
use Date::Manip;

use lib "/usr/local/lib/perl";
use cpi_file qw( fatal echodo read_lines write_lines append_file
		    files_in cleanup );
use cpi_arguments qw( parse_arguments );
use cpi_send_file qw( sendmail );
use cpi_time qw( parsedate revlocaltime time_string );
use cpi_translate qw( xprint );
use cpi_cgi qw( CGIreceive CGIheader );
use cpi_user qw( logout_select );
use cpi_setup qw( setup );
use cpi_inlist qw( inlist );
use cpi_db qw( dbget );
use cpi_trace qw( stack_trace );

use Data::Dumper;

package main;

#print "Content-type:  text/html\n\n";
$| =	1;

&setup( stderr=>"Sched" );

# Put constants here

my %MAIL_ON_DAYS =
    (
    "Non recurring"	=> [ 0, 1, 2, 7, 14, 30, 60 ],
    "Recurring"		=> [ 0, 1, 2, 7 ]
    );
my $DAY_IN_SECONDS	=	( 60 * 60 * 24 );
#my $FROM		=	"reminder\@brightsands.com";
my $FROM		=	"chris";

my $SENDMAIL		=	"/usr/lib/sendmail";
my $MAIL		=	"/usr/bin/Mail";
my $SECONDS_PER_DAY	=	86400;
my $FORM_NAME		=	"form";

my $UnixDateOffset	=	18000;
my $TMP			=	"/tmp/$cpi_vars::PROG.tmp";

my %entries;
my ($tyear,$tmonth,$tmday,$thour,$tmin,$tsec,$twday);
my %start_at;
my %stop_at;

our %ONLY_ONE_DEFAULTS	=
    (
    "datetime"		=>	time(),
    "source"		=>	"",
    "directory"		=>	$cpi_vars::BASEDIR."/schedules",
    "backups"		=>	$cpi_vars::BASEDIR."/lib/bups",
    "newfile"		=>	$cpi_vars::BASEDIR."/lib/remind.new",
    "users"		=>	"all",
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
#########################################################################
sub sanity
    {
    my( $msg ) = @_;
    my @yearps= @{$entries{"chris.interim\@gmail.com"}{year}{2026}};
    print "year ",( map{$_->{record}} grep( $_->{rest}=~/SEARCHFOR/, @yearps )), ".\n";
    my @monps= @{$entries{"chris.interim\@gmail.com"}{mon}{11}};
    print "mon ",( map{$_->{record}} grep( $_->{rest}=~/SEARCHFOR/, @monps )), ".\n";
    my @dayps= @{$entries{"chris.interim\@gmail.com"}{day}{1}};
    print "day ",( map{$_->{record}} grep( $_->{rest}=~/SEARCHFOR/, @dayps )), ".\n";
    print "[$msg] nyear=",scalar(@yearps)," nmon=",scalar(@monps)," nday=",scalar(@dayps),".\n";
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
#	Return a list of schedules to process.				#
#########################################################################
sub schedule_list
    {
    if( ! $ARGS{users} || $ARGS{users} eq "all" )
        { return &files_in( $ARGS{directory},".*@.*" ); }
    else
        { return split(/\s*,\s*/,$ARGS{users}); }
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
    #print "cmc whenstr=[$whenstr] [$rest]\n";
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
    printf( "%s %d %s %s %s\n", $address, $entry->{record}, $entry->{whenstr}, $entry, $entry->{rest} )
	if( $ARGS{verbosity} > 1 );
    return $entry;
    }

#########################################################################
#	Parse a line from remind file or from web form.  Return pointer	#
#	to new entry if it was real or undef if we don't recognize it.	#
#########################################################################
sub parse_entry
    {
    my( $address, $entry_text ) = @_;
    my( $mon, $day, $yr, $every, $rest );
    if( $entry_text =~ m~^(\d\d\d\d)-(\d\d*)-(\d\d*):(\d+)\s*(.*?)$~ ||
	$entry_text =~ m~^(\d\d\d\d|\*)-(\d\d*|\*)-(\d\d*|\*)(\s*)(.*?)$~ )
	{ ($yr,$mon,$day,$every,$rest) = ($1,$2,$3,$4,$5); }
    elsif( $entry_text =~ m~^(\d+)/(\d+)/(\d+):(\d+)\s*(.*)$~ ||
	$entry_text =~ m~^(\d+|\*)/(\d+|\*)/(\d+|\*)(\s+)(.*)$~	)
	{ ($mon,$day,$yr,$every,$rest) = ($1,$2,$3,$4,$5); }
    else
        { return undef; }

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
    $entry->{input} = $entry_text;
    my @current_entries = ( $entry );

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
    return @current_entries;
    }

#########################################################################
#	Determine names from arguments.					#
#########################################################################
sub user_address_file
    {
    $| = 1;
    my %uaf = ();

    foreach my $arg ( @_ )
        {
	if( $arg =~ /\// )
	    { $uaf{file} = $arg; }
	elsif( $arg =~ /@/ )
	    { $uaf{address} = $arg; }
	else
	    { $uaf{user} = $arg; }
	}

    $uaf{user} = $cpi_vars::USER if( (!defined($uaf{user})) && $cpi_vars::USER );

    if( ! defined($uaf{address}) )
	{
	if( $uaf{user} )
	    {
	    $uaf{address} =
		&dbget($cpi_vars::ACCOUNTDB,"users",$uaf{user},"email");
	    }
	elsif( $uaf{file} )
	    {
	    $uaf{address} = $uaf{file};
	    $uaf{address} =~ s+.*/++;
	    }
	}

    $uaf{file} = "$ARGS{directory}/$uaf{address}" if(!$uaf{file});
    #print STDERR "End uaf...<br>\n", (map {"k($_)=$uaf{$_}.<br>\n"} keys %uaf );

    return %uaf;
    }

#########################################################################
#	Read remind file into %entries (and set destination address).	#
#########################################################################
sub read_remind_file
    {
    my %uaf = &user_address_file( @_ );
    my @current_entries;

    foreach my $input ( &read_lines( $uaf{file} ) )
	{
	if( defined($input) and $input ne "" )
	    {
	    my @new_entries;
	    if( $input =~ /^[^\s@]+@[\w\.]+\.\w+$/ )
		{ $uaf{address} = $input; }
	    elsif( @new_entries = &parse_entry( $uaf{address}, $input ) )
		{ @current_entries = @new_entries; }
	    elsif( @current_entries )
		{
		grep( $_->{rest}.=$input, @current_entries );
		}
	    else
		{ print "'$input' not connected to an entry.  Skipping.\n"; }
	    }
	}
    #print "remind:\n", Dumper(\%entries), "\n";
    }

#########################################################################
#	Go through entrys hash figuring out e-mail.			#
#########################################################################
sub generate_message
    {
    my( $mode, @rest ) = @_;
    my %uaf = &user_address_file( @rest );
    &read_remind_file( @rest );
    my $now = $ARGS{datetime};
    #my $now_day = $ARGS{datetime} - ($ARGS{datetime} % $DAY_IN_SECONDS);
    my $now_day = $ARGS{datetime};

    print "generate_message now_day="
        .&time_string("%04d-%02d-%02d %02d:%02d:%02d.%d.\n",$now_day)
	if( $ARGS{verbosity} > 1 );

    my $address = $uaf{address};
    my $last_header = "";
    my $txt = "";
    my $found = 0;
    foreach my $entry_type (
	sort {scalar(@{$MAIL_ON_DAYS{$a}}) <=> scalar(@{$MAIL_ON_DAYS{$b}}) }
	    keys %MAIL_ON_DAYS)
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
		&matching_entries($uaf{address},$cyear,$cmonth,$cmday) )
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
	print "Debug Mail -s '$subject' $uaf{address}\n",
	    ( $txt ? $txt : "$subject\n" );
	}
    elsif( $mode eq "mail" )
	{
	&sendmail( $FROM, $uaf{address}, $subject, $txt );
	}
    elsif( $MAIL )
	{
	#print "Mail subject=[$subject] address=[$uaf{address}]\n";
	open(OUT, "|Mail -s '$subject' $uaf{address}")
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
To:  $uaf{address}
Subject:  $subject

$txt
MAILEOF
	close(OUT);
	}
    }

#########################################################################
#	Read file in and sort it.					#
#########################################################################
sub do_sort
    {
    my %uaf = &user_address_file(@_);

    my @toprint = ( $uaf{address} );

    foreach my $ep ( sort { $a->{whenstr} cmp $b->{whenstr} }
	grep( ! $_->{interpolated} && $_->{rest},
	    @{$entries{$uaf{address}}{all}} ) )
	{
	push( @toprint, $ep->{whenstr} . " " . $ep->{rest} );
	}

    if( $ARGS{mode} eq "sort" )
        { &write_lines( $ARGS{newfile}, @toprint ); }
    else
        {
        my $bup = &time_string("%04d-%02d-%02d:%02d:%02d:%02d.bz2",time());
	&echodo( "bzip2 -9 < $uaf{file} > $ARGS{backups}/$bup" );
	&write_lines( $uaf{file}, @toprint );
	}

    if( $ARGS{verbosity} )
	{	# This will not happen with web app
	print "size of $uaf{file} = ", -s $uaf{file}, ".\n";
	print "size of $ARGS{newfile} = ", -s $ARGS{newfile}, ".\n";
	}
#    &fatal("Sorting from $ARGS{newfile} to $ARGS{file} caused a corruption.")
#        if( -s $ARGS{file} != -s $ARGS{newfile} );
#    &echodo("cat '$ARGS{newfile}' > '$ARGS{file}' && rm -f '$ARGS{newfile}'");
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
    my %uaf = &user_address_file();

    &setup_time_report(@klist);
    #my( $start_at, $stop_at ) = &setup_time_report(@klist);

    my @toprint = ( "<input type=hidden name=key><table border=1><tr>",
        join( "", map { "<th>XL(${_}day)</th>" }
	    ("Sun","Mon","Tues","Wednes","Thurs","Fri","Satur") ) );
    
    #my $now = time();
    #my($tyear,$tmonth,$tmday) = &epoch_to_ymd($now);

    foreach my $address ( $uaf{address} )
	{
	my($cyear,$cmonth,$cmday,$chour,$cmin,$csec,$wday)
	    = ( $tyear, $tmonth, $tmday, $thour, $tmin, $tmday );
	if( $here )
	    {
	    if( $here =~ m:^(\d\d\d\d)-(\d+)-(\d+)$: )
	        { $tyear=$1; $tmonth=$2; $tmday=$3; }
	    elsif( $here =~ m:^([01]\d)/([0123]\d)/(\d\d\d\d)$: )
	        { $tyear=$3; $tmonth=$1; $tmday=$2; }
	    elsif( $here =~ m:^([0123]\d)/([01]\d)/(\d\d\d\d)$: )
	        { $tyear=$3; $tmonth=$1; $tmday=$2; }
	    elsif( $here =~ m:^([01]\d)/([0123]\d)/(\d\d)$: )
	        { $tyear=$3+2000; $tmonth=$1; $tmday=$2; }
	    elsif( $here =~ m:^([0123]\d)/([01]\d)/(\d\d)$: )
	        { $tyear=$3+2000; $tmonth=$1; $tmday=$2; }
	    $cyear=$tyear; $cmonth=$tmonth; $cmday=$tmday;
	    }
	    #= epoch_to_ymd($start_at{$uaf{address}});
#	printf("ymd($start_at{$uaf{address}}}=%04d-%02d-%02d %02d:%02d:%02d %d.\n",
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
	    elsif( $timeind < $ARGS{datetime} )
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
		&matching_entries($uaf{address},$cyear,$cmonth,$cmday) )
		{
		foreach my $entry (
		    sort {$a->{hhmm} cmp $b->{hhmm}} @entries_today )
		    {
		    push( @toprint, "<br>",
			( $entry->{hhmm} ? $entry->{hhmm}." " : "* " ),
			"<a href='javascript:get_an_entry(\"$datetext\",\"$entry->{rest}\");'>",
			$entry->{rest},
			"</a>" ) if( $entry->{rest} );
		    }
		}
	    push( @toprint, "</td>" );
	    $timeind += $SECONDS_PER_DAY;
	    $check_year = $cyear;
	    $check_month = $cmonth;
	    ($cyear,$cmonth,$cmday,$chour,$cmin,$csec,$wday)
		= &epoch_to_ymd($timeind);
	    } while( $timeind<=$stop_at{$uaf{address}} || $cmonth==$check_month );
	}
    push( @toprint, "</tr>\n<tr><th colspan=7>",
	"<input type=text name=here value='",
	$cpi_vars::FORM{here},
	"' size=10>",
	"</th></tr></table></form>\n" );
    #print STDERR "Returning [",@toprint,"]\n";
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
    my %uaf = &user_address_file();

    $cpi_vars::FORM{here} ||= &time_string("%04d-%02d-%02d");
    $cpi_vars::FORM{new_entry} ||= "";
    $cpi_vars::FORM{old_entry} ||= "";
    if( $cpi_vars::FORM{new_entry} && ! $cpi_vars::FORM{old_entry} )
        {
	&append_file( $uaf{file},
	    sprintf("%10s %s\n",
		$cpi_vars::FORM{here}, $cpi_vars::FORM{new_entry} ) );
	&read_remind_file( $uaf{address} );
	}
    else
        {
	&read_remind_file( $uaf{address} );
	if( $cpi_vars::FORM{new_entry} ne $cpi_vars::FORM{old_entry} )
	    {
	    foreach my $entry (
		&matching_entries($uaf{address},split(/-/,$cpi_vars::FORM{here}) ) )
		{
		$entry->{rest} = $cpi_vars::FORM{new_entry}
		    if( $entry->{rest} eq $cpi_vars::FORM{old_entry} );
		}
	    &do_sort( $uaf{address} );	# Write out the now modified data
	    }
	}

    my $toprint = <<EOF . &calendar() . "</center>";
<script>

//////////////////////////////////////////////////////////////////////////
//	User wants to change or add an entry.				//
//////////////////////////////////////////////////////////////////////////
function get_an_entry( datestr, old_entry )
    {
    with ( window.document )
        {
	var prompt_val = "XL(Enter entry for) "+datestr;
	var new_value =
	    ( typeof old_entry === 'undefined'
	    ? prompt(prompt_val)
	    : prompt(prompt_val,old_entry) );
	if( new_value !== null )
	    {
	    $FORM_NAME.here.value = datestr;
	    $FORM_NAME.new_entry.value = new_value;
	    $FORM_NAME.old_entry.value =
		( typeof old_entry === 'undefined' ? "" : old_entry );
	    $FORM_NAME.submit();
	    }
	}
    }
</script>

</head><body $cpi_vars::BODY_TAGS>
$cpi_vars::HELP_IFRAME
<form name=$FORM_NAME method=post>
<input type=hidden name=SID value=$cpi_vars::SID>
<input type=hidden name=USER value=$cpi_vars::USER>
<input type=hidden name=func value=Update>
<input type=hidden name=new_entry>
<input type=hidden name=old_entry>
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


if( $ENV{SCRIPT_NAME} || $ARGS{mode} eq "html" )
    { &userpage_handler(); }
elsif( $ARGS{mode} eq "sort" )
    { grep( &do_sort($_), &schedule_list() ); }
elsif( &inlist($ARGS{mode},"mail","show") )
    { grep( &generate_message($ARGS{mode},$_), &schedule_list() ); }

exit($exit_stat);
