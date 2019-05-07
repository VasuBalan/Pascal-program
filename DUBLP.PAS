{$R-}    {Range checking off}
{$B+}    {Boolean complete evaluation on}
{$S+}    {Stack checking on}
{$I+}    {I/O checking on}
{$N-}    {No numeric coprocessor}
{$M 65500,16384,655360} {Turbo 3 default stack and heap}

{         <t>Dual Upper Bounding Linear Programming Routine }
program dublp;

{  Dual Upper Bound Linear Programming Algorithm
        for use with POWER GENERATION OPERATION AND CONTROL
            Allen J. Wood & Bruce F. Wollenberg    }


Uses
  Crt,
  Printer;

label quit;

const

        itermax : integer = 40;
        toler   : real    = 1.0e-06;
        maxvar  : integer = 50;
        maxcon  : integer = 20;
        IOVal   : Integer = 0;
        IOErr   : Boolean = False;

type

        varrange = 1..50;
        constrange = 1..20;

var

        numvar, orig_numvar, ivar, numcon, icon, iter,
        pivot_row, pivot_col, linenumber,
        max_violated_variable  : integer;

        maxviolation, bcost, c_constant  :  real;

        filename : string[ 25 ];
        binding : string[10];

        inputfile : text;
        inputchar : char;

        title1, title2 : string[80];

        diagnostics, print_output, feasible : boolean;

        basis : array [varrange] of integer;
        basis_out : array [varrange] of integer;

        x, xmin, xmax, c : array [varrange] of real;

        constraint_type : array[constrange] of char;

        a      : array [constrange,varrange] of real;
        orig_a : array [constrange,varrange] of real;

        b      : array [constrange] of real;
        orig_b : array [constrange] of real;

        equal_constraint_slack : array[varrange] of boolean;

        variable_label : array[varrange] of string[40];



{----------------------------------------------------------------------------}
{$I-,R-}
{ <f> <s>   IO Check routine }
procedure IOCheck( linenumber : integer );

      {This routine sets IOErr equal to IOresult, then sets
       IOFlag accordingly.  It also prints out a message on
       the 24th line of the screen.}

var
  Ch                   : Char;
begin
  IOVal := IOresult;
  IOErr := (IOVal <> 0);
  GotoXY(1,24); ClrEol;        { Clear error line in any case }
  if IOErr then begin
    Write(Chr(7));
    case IOVal of
        2  :  Writeln('File does not exist');
        3  :  Writeln('Path not found  ');
        4  :  Writeln('Too many files open ');
        5  :  Writeln('File access denied ');
       12  :  Writeln('Invalid file access code ');
       15  :  Writeln('Invalid drive number ');
      100  :  Writeln('Disk read error ');
      101  :  Writeln('Disk write error ');
      102  :  Writeln('File not assigned ');
      103  :  Writeln('File not open');
      104  :  Writeln('File not open for input');
      105  :  Writeln('File not open for output');
      106  :  Writeln('Error in numeric format');
      150  :  Writeln('Disk is write protected');
      151  :  Writeln('Unknown unit');
      152  :  Writeln('Drive not ready');
      153  :  Writeln('Unknown command ');
      154  :  Writeln('CRC error in data ');
      155  :  Writeln('Bad drive structure length ');
      156  :  Writeln('Disk seek error ');
      157  :  Writeln('Unknown media type ');
      158  :  Writeln('Selector not found ');
      159  :  Writeln('Printer out of paper ');
      160  :  Writeln('Device write fault ');
      161  :  Writeln('Device read fault ');
      162  :  Writeln('Hardware failure ');
    else      Writeln('Unknown I/O error:  ',IOVal:3)
    end;
    writeln( ' error on line ', linenumber, ' of input file ')
  end
end; { of proc IOCheck }


{----------------------------------------------------------------------------}


procedure print_file_and_title(var outfile:text);

begin
  writeln(outfile);
  writeln(outfile,' file: ',filename );
  writeln(outfile);
  writeln(outfile,title1);
  writeln(outfile,title2);
end; { End procedure }

{----------------------------------------------------------------------------}

procedure print_input_data( var outfile:text);

var
  i,j,icol : integer;

begin
  writeln(outfile);
  writeln(outfile,' Number of variables = ',numvar );
  writeln(outfile,' Numbar of constraints = ', numcon );
  writeln(outfile);
  writeln(outfile,'Objective function');
  icol := 1;
  for j := 1 to numvar do
      begin
      if icol = 6 then
         begin
         icol := 1;
         writeln(outfile)
         end;
      write(outfile, c[j]:7,'  ');
      icol := icol + 1
      end;
  writeln(outfile);
  for i := 1 to numcon do
      begin
      icol := 1;
      writeln(outfile);
      writeln(outfile,'Constraint ',i);
      for j := 1 to numvar do
        begin
        if icol = 6 then
          begin
          icol := 1;
          writeln(outfile)
          end;
        write(outfile, a[i,j]:7,'  ');
        icol := icol + 1
        end;
        write(outfile,'   ', constraint_type[i],'   ');
        writeln(outfile, b[i]:7 );
        writeln(outfile)
      end;
  for i := 1 to numvar do writeln(outfile, i, xmax[i], xmin[i] );
end;

{----------------------------------------------------------------------------}
{ <f> <s>   Data Input Routine }

procedure datainput;

label quit;

var i,j : integer;

begin
        diagnostics := false;
        write( ' DO YOU WANT DIAGNOSTIC OUTPUT ? (Y or N) ');
        readln( inputchar );
        if (inputchar = 'Y') or (inputchar = 'y') then diagnostics := true;
        writeln;
        print_output := false;
        write( ' DO YOU WANT OUTPUT ON PRINTER? (Y or N) ');
        readln( inputchar );
        if (inputchar = 'Y') or (inputchar = 'y') then print_output := true;
        writeln;
        linenumber := 0;
        write ( ' ENTER NAME OF INPUT DATA FILE :' );
        readln( filename );
        assign( inputfile, filename );      iocheck(linenumber);
                                            if ioerr then goto quit;
        reset( inputfile );      iocheck(linenumber);
                                 if ioerr then goto quit;

{ Zero out input arrays }

        for i := 1 to maxvar do
        begin
                xmax[i] := 0.0;
                xmin[i] := 0.0;
                x[i] := 0.0;
                basis[i]:= 0;
                c[i]    := 0.0;
                equal_constraint_slack[i] := false;
        end;
        for i := 1 to maxcon do
        begin
                b[i] := 0.0;
                for j := 1 to maxvar do a[i,j] := 0.0;
        end;

        iter := 0;                  

{ Read first line of file }

        linenumber := linenumber + 1;
        readln( inputfile, title1 );      iocheck(linenumber);
                                          if ioerr then goto quit;
        linenumber := linenumber + 1;
        readln( inputfile, title2 );      iocheck(linenumber);
                                          if ioerr then goto quit;
        linenumber := linenumber + 1;
        readln( inputfile, numvar, numcon );      iocheck(linenumber);
                                                  if ioerr then goto quit;

{ Read objective function coefficients }

        linenumber := linenumber + 1;
        for i := 1 to numvar -1 do
        begin
                read( inputfile, c[i] );      iocheck(linenumber);
                                              if ioerr then goto quit;
        end;
        readln( inputfile, c[numvar] );       iocheck(linenumber);
                                              if ioerr then goto quit;
        readln( inputfile, c_constant );      iocheck(linenumber);
                                              if ioerr then goto quit; 

{ Read constraint data }

        for i := 1 to numcon do
        begin
                linenumber := linenumber + 1;
                for j := 1 to numvar do
                begin
                        read( inputfile, a[i,j] );      iocheck(linenumber);
                                                        if ioerr then goto quit;
                end;
        repeat
                read( inputfile, inputchar );      iocheck(linenumber);
                                                   if ioerr then goto quit;
        until inputchar <> ' '; constraint_type[i] := inputchar;
        readln( inputfile, b[i] );      iocheck(linenumber);
                                        if ioerr then goto quit;
        end;

{ Save original A matrix and orig b vector}

        for i := 1 to numcon do
        begin
          orig_b[i] := b[i];
          for j := 1 to numvar do
          begin
           orig_a[i,j] := a[i,j];
          end;
        end;

{ Read in upper and lower variable bounds }

        for i := 1 to numvar do
        begin
        linenumber := linenumber + 1;        
        readln( inputfile, ivar, xmin[i], xmax[i], variable_label[i] );
                                 iocheck(linenumber);
                                 if ioerr then goto quit;
        end;

        close( inputfile );      iocheck(linenumber);
                                 if ioerr then goto quit;

if print_output then print_file_and_title(lst)
                else print_file_and_title(output);

if diagnostics then 
        if print_output then print_input_data(lst)
                        else print_input_data(output);
         
quit :

end;   { end of data input }


{----------------------------------------------------------------------------}
{ <f> <s>   Diagnostic Dump Routine }
procedure diagnostic_dump;

{ diagnostic dump of tableau and other variable values }
{ This routine was used to degub the program, at present it is }
{ not called from anywhere in this program, it is left here }
{ in case someone wants to rework the program }

var sum, z : real;

begin

sum := 0.0;
for ivar := 1 to numvar do sum := sum + c[ivar] * x[ivar];
z := sum - bcost ;
writeln(lst, ' ITER = ', iter, '  COST = ', z );
for icon := 1 to numcon do
    begin
    writeln(lst, 'A',icon );
    for ivar := 1 to numvar do
        write(lst, a[icon,ivar]:7,'  ');
    writeln(lst,'  B',icon, '  ',b[icon]:7);
    end;

writeln(lst, 'C');
for ivar := 1 to numvar - 1 do
    write(lst, c[ivar]:7,'  ');
    writeln(lst, c[numvar]:7);

writeln(lst, 'XMIN');
for ivar := 1 to numvar - 1 do
    write(lst, xmin[ivar]:7,'  ');
    writeln(lst, xmin[numvar]:7);

writeln(lst, 'XMAX');
for ivar := 1 to numvar - 1 do
    write(lst, xmax[ivar]:7,'  ');
    writeln(lst, xmax[numvar]:7);

writeln(lst, 'X');
for ivar := 1 to numvar - 1 do
    write(lst, x[ivar]:7,'  ');
    writeln(lst, x[numvar]:7);

writeln(lst, 'BASIS');
for ivar := 1 to numvar - 1 do
    write(lst, basis[ivar]:7,'  ');
    writeln(lst, basis[numvar]:7);

end;  { end of diagnostic dump }

{----------------------------------------------------------------------------}
{ <f> <s>   Solution Dump Routine }
procedure solution_dump( var outfile:text );


var z, sum : real ;
    con_violated : integer;

begin

sum := 0.0;
for ivar := 1 to numvar do sum := sum + c[ivar] * x[ivar];
z := sum - bcost ;
writeln(outfile); writeln(outfile,'    ITER = ', iter, '  COST = ', z ); 

if diagnostics then
begin
for ivar := 1 to numvar do
    begin
    if basis[ivar] <> 0 then
        begin
        if x[ivar] > xmax[ivar] then 
            begin 
            con_violated := basis[ivar];
            writeln(outfile,' constraint ',con_violated,' violation = ',
                            x[ivar] - xmax[ivar] );
            end;
        if x[ivar] < xmin[ivar] then
            begin
            con_violated := basis[ivar];
            writeln(outfile,' constraint ',con_violated,' violation = ',
                            xmin[ivar] - x[ivar] )
            end;
        end;
    end;
end;

end;  { end solution dump }

{----------------------------------------------------------------------------}
{ <f> <s>   Tableau Setup  }
procedure tableau_setup;

var last_reg_variable, slackvar : integer;
    sum : real;

begin

orig_numvar := numvar;   {remember the original number of variables}

{ add one slack variable to tableau for each constraint }

for icon := 1 to numcon do
    begin
    numvar := numvar + 1;          { increment numvar to include slack }
    if constraint_type[icon] = '=' then
        { set up slack for equality constraint }
        begin
        a[icon, numvar] := 1.0;
        xmax[numvar] := 0.0;
        xmin[numvar] := 0.0;
        equal_constraint_slack[numvar] := true;
        end;
    if constraint_type[icon] = '<' then
        { set up slack for less than constraint }
        begin
        a[icon, numvar] := 1.0;
        xmax[numvar] := 1.0E+9;
        xmin[numvar] := 0.0
        end;
    if constraint_type[icon] = '>' then
        { set up slack for greater than constraint}
        begin
        a[icon, numvar] := 1.0;
        xmax[numvar] := 0.0;
        xmin[numvar] := -1.0E+9;
        end;
    end;

{  set up variables to start at mininum if cost coefficient is positive and
   at maximum if cost coefficient is negative }

for ivar := 1 to numvar do
    begin
    if c[ivar] >= 0.0  then x[ivar] := xmin[ivar]
                       else x[ivar] := xmax[ivar];
    basis_out[ivar] := 0;
    end;

last_reg_variable := numvar - numcon;

{ set up value of each slack variable to balance out each constraint }

for icon := 1 to numcon do
    begin
    sum := b[icon];
    for ivar := 1 to last_reg_variable do
           begin
           sum := sum - a[icon,ivar] * x[ivar];
           end;
    slackvar := last_reg_variable + icon;
    x[slackvar] := sum / a[icon,slackvar] ;
    basis[slackvar] := icon;
    end;

end;    { end of tableau setup }

{----------------------------------------------------------------------------}
{ <f> <s>   Find Max Violated Variable  }
procedure find_max_violated_variable( var max_violated_variable : integer;
                                      var maxviolation : real );

{ finds the variable that has the maximum violation, ie the maximum amount
  outside its upper or lower limit. If max_violated_variable returns a zero
  then all variables are within limit and the LP has been solved. }

var violation : real;
    violation_found : boolean;

begin

max_violated_variable := 0;
maxviolation := 0.0;
violation_found := false;

for ivar := 1 to numvar do
    begin
    if basis[ivar] <> 0 then
        begin
        { test for less than variable minimum}
        if x[ivar] <= ( xmin[ivar] - toler ) then
            begin
            violation := xmin[ivar] - x[ivar];
            violation_found := true;
            end;
        { test for greater than variable maximum }
        if x[ivar] >= ( xmax[ivar] + toler ) then
            begin
            violation := x[ivar] - xmax[ivar];
            violation_found := true;
            end;
        { see if violation is maximum yet found }
        if ( violation_found and
            ( violation > maxviolation) ) then
            begin
            maxviolation := violation;
            max_violated_variable := ivar;
            end;
        end;
    end;

end;  { end of find_max_violated_variable }

{----------------------------------------------------------------------------}
{ <f> <s>   Determine Pivot Column  }
procedure determine_pivot_column( var feasible : boolean;
                                  var max_violated_variable,
                                      pivot_row, pivot_col   : integer );

{ determines the pivot column by testing each non basis variable for
  validity as a candidate variable. If no variable is found the LP is
  infeasible and the variable "feasible" is set false. }

var min_cdiva : real; { this variable contains the minimum of the ratio c/a }
    amax, cdiva : real;
    candidate : boolean;

begin

pivot_row := basis[ max_violated_variable ];
pivot_col := 0;

if x[max_violated_variable] < xmin[max_violated_variable] then
    { logic to select pivot column when most violated variable is
      less than its minimum, Col selection logic P1 in text }
    begin
    min_cdiva := 1.0E+9 ;
    amax := 0.0;
    for ivar := 1 to numvar do
        begin
        candidate := true ;
        { test for valid candidate variable }
        if basis[ivar] <> 0 then candidate := false;
        if basis_out[ivar] > 5 then 
           begin
           candidate := false;
           basis_out[ivar] := 0;
           end;
        if ( (equal_constraint_slack[ivar]) and (x[ivar]=0) ) then
                                                         candidate := false;
        if abs( a[pivot_row, ivar] ) < toler then candidate := false;
        if candidate then
            begin
            { further tests for valid candidate variable}
            if ( ( (x[ivar] = xmin[ivar])     and
                   (a[pivot_row,ivar] < 0.0)  and
                   (c[ivar] >= 0.0)               )
               or
               (   (x[ivar] = xmax[ivar])     and
                   (a[pivot_row,ivar] > 0.0)  and
                   (c[ivar] <= 0.0)               ) ) then
                begin
                (*writeln(lst,' ivar x a[piv,ivar] c ',ivar,'  ',  
                   x[ivar]:8,'  ',a[pivot_row,ivar]:8,'  ',c[ivar]:8);*)
                { test for best variable to become pivot column }
                if c[ivar] <> 0.0 then
                    begin
                    cdiva := c[ivar] / ( -1.0*a[pivot_row,ivar] );
                    (*writeln(lst,' cdiva ',cdiva );*)
                    if cdiva < min_cdiva then
                       begin
                       min_cdiva := cdiva;
                       pivot_col := ivar;
                       end;
                    end
                else if abs( a[pivot_row,ivar] ) > amax then
                    begin
                    amax := a[pivot_row,ivar];
                    pivot_col := ivar;
                    min_cdiva := 0.0 ;
                    end;
                end;
            end;
        end;
     end
else if x[max_violated_variable] > xmax[max_violated_variable] then
    { logic to select pivot column when most violated variable is
      greater than its maximum, col selection logic P2 in text }
    begin
    min_cdiva := 1.0E+9 ;
    amax := 0.0 ;
    for ivar := 1 to numvar do
        begin
        candidate := true ;
        { test for valid candidate variable }
        if basis[ivar] <> 0 then candidate := false;
        if basis_out[ivar] > 5 then 
           begin
           candidate := false;
           basis_out[ivar] := 0;
           end;
        if ( (equal_constraint_slack[ivar]) and (x[ivar]=0) ) then
                                                      candidate := false;
        if abs( a[pivot_row, ivar] ) < toler then candidate := false;
        if candidate then
            begin
            { further tests for valid candidate variable}
            if ( ( (x[ivar] = xmin[ivar])     and
                   (a[pivot_row,ivar] > 0.0)  and
                   (c[ivar] >= 0.0)               )
               or
               ( (x[ivar] = xmax[ivar])     and
                 (a[pivot_row,ivar] < 0.0)  and
                 (c[ivar] <= 0.0)               ) ) then
                begin
                (*writeln(lst,' ivar x a[piv,ivar] c ',ivar,'  ',
                     x[ivar]:8,'  ',a[pivot_row,ivar]:8,'  ',c[ivar]:8);*)
                { test for best variable to become pivot column }
                if c[ivar] <> 0.0 then
                    begin
                    cdiva := c[ivar] / a[pivot_row,ivar] ;
                    (*writeln(lst,' cdiva ',cdiva );*)
                    if cdiva < min_cdiva then
                       begin
                       min_cdiva := cdiva;
                       pivot_col := ivar;
                       end;
                    end
                else if abs( a[pivot_row,ivar] ) > amax then
                    begin
                    amax := a[pivot_row,ivar];
                    pivot_col := ivar;
                    min_cdiva := 0.0 ;
                    end;
                end;
            end;
        end;
    end;

{ set feasible pivot column flag }

if pivot_col <> 0 then feasible := true
                  else feasible := false;

end;    { end of determine_pivot_column }

{----------------------------------------------------------------------------}
{ <f> <s>   Pivot and Switch }
procedure pivot_and_switch( var pivot_row, pivot_col : integer );

{ performs pivot operation, switches variables in and out of basis, and
  calculates value of new variables }

var sum : real;
    basis_col : integer;

  procedure print_pivot( var outfile:text );
  begin
  writeln(outfile,' pivot row = ',pivot_row:4,'   pivot col = ', pivot_col:4 );
  end; { End procedure }

begin

if print_output then print_pivot(lst)
                else print_pivot(output);

{ normalize pivot row of a matrix and b vector by dividing by pivot element }

for ivar := 1 to numvar do
    begin
    if ivar <> pivot_col then
        begin
        a[pivot_row,ivar] := a[pivot_row,ivar] / a[pivot_row,pivot_col];
        if abs( a[pivot_row,ivar] )< toler then a[pivot_row,ivar] := 0.0 ;
        end;
    end;
b[pivot_row] := b[pivot_row] / a[pivot_row,pivot_col];
if abs( b[pivot_row] ) < toler then b[pivot_row] := 0.0;
a[pivot_row,pivot_col] := 1.0;

{ put matrix into cannonical form with respect to pivot column }

for icon := 1 to numcon do
    begin
    if icon <> pivot_row then
        begin
        for ivar := 1 to numvar do
            begin
            if ivar <> pivot_col then
                begin
                a[icon,ivar] := a[icon,ivar]
                                - a[pivot_row,ivar] * a[icon,pivot_col];
                if abs( a[icon,ivar] ) < toler then a[icon,ivar] := 0.0;
                end;
            end;
        b[icon] := b[icon] - b[pivot_row] * a[icon,pivot_col];
        if abs( b[icon] ) < toler then b[icon] := 0.0;
        a[icon,pivot_col] := 0.0;
        end;
    end;

{ adjust cost row to reflect pivot }

for  ivar := 1 to numvar do
    begin
    if ivar <> pivot_col then
        begin
        c[ivar] := c[ivar] - a[pivot_row,ivar] * c[pivot_col] ;
        if abs( c[ivar] ) < toler then c[ivar] := 0.0;
        end;
    end;
bcost := bcost - b[pivot_row] * c[pivot_col];
c[pivot_col] := 0.0;

{ switch basis variables }

if x[max_violated_variable] < xmin[max_violated_variable] then
    x[max_violated_variable] := xmin[max_violated_variable];
if x[max_violated_variable] > xmax[max_violated_variable] then
    x[max_violated_variable] := xmax[max_violated_variable];
basis[max_violated_variable] := 0 ;
basis_out[max_violated_variable] := basis_out[max_violated_variable] + 1;
basis[pivot_col] := pivot_row ;

{ calculate new values for all basis variables }

for icon := 1 to numcon do
    begin
    sum := b[icon];
    for ivar := 1 to numvar do
        begin
        if basis[ivar] = 0 then sum := sum - a[icon,ivar] * x[ivar]
        else if basis[ivar] = icon then basis_col := ivar;
        end;
    x[basis_col] := sum;
    if abs( x[basis_col] ) < toler then x[basis_col] := 0.0;
    end;

end;   { end pivot and switch }

{----------------------------------------------------------------------------}
{ <f> <s>   Output Solution }
procedure output_solution( var outfile:text);

{ output the solution }

var sum : real;

begin
    writeln(outfile);
    writeln(outfile,' SOLUTION ');
    writeln(outfile,
        '         XMIN         X            XMAX       VARIABLE DESCRIPTION ');
    for ivar := 1 to numvar - numcon do
        begin
        writeln(outfile, ivar:2,'  ', xmin[ivar]:11:4,'  ', x[ivar]:11:4,'  ',
                  xmax[ivar]:11:4, variable_label[ivar] )
        end;

writeln(outfile);
writeln(outfile,' CONSTRAINTS ');
writeln(outfile,
        'CONSTRAINT   SUM A*X           B  ');
for icon := 1 to numcon do
    begin
    sum := 0.0;
    binding := '       ';
    for ivar := 1 to orig_numvar do
      begin
      sum := sum + orig_a[icon,ivar]*x[ivar];
      {writeln(outfile, orig_a[icon,ivar], '  ',x[ivar]);}
      end;
    if abs(sum - orig_b[icon])<0.001 then binding := 'BINDING';
    write(outfile, icon:2,'       ',sum:11:4,'  ',constraint_type[icon],'  ');
    writeln(outfile, orig_b[icon]:11:4,'     ',binding);
    end;


end;  { end of output solution }
{----------------------------------------------------------------------------}
{ <f> <s>   Main Program }

begin  { begin main program }

datainput;
   if ioerr then goto quit;
tableau_setup;

if print_output then solution_dump(lst)
                else solution_dump(output);

{ iterative loop to solve LP }

iter := 0;
bcost := -1.0 * c_constant;
repeat
    begin
    iter := iter + 1;
    find_max_violated_variable( max_violated_variable, maxviolation );
    if max_violated_variable <> 0 then
        begin
        determine_pivot_column( feasible, max_violated_variable,
                                pivot_row, pivot_col );
        if feasible then pivot_and_switch( pivot_row, pivot_col );
          if print_output then solution_dump(lst)
                          else solution_dump(output);
        end;
    end;
until ( ( iter = itermax ) or
        ( max_violated_variable = 0 ) or
        ( feasible = false) ) ;

if not feasible then writeln( ' infeasible solution ' );

if feasible then 
   if print_output then output_solution(lst)
                   else output_solution(output);

quit :

END.

