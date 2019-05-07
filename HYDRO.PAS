{$R-}    {Range checking off}
{$B+}    {Boolean complete evaluation on}
{$S+}    {Stack checking on}
{$I+}    {I/O checking on}
{$N-}    {No numeric coprocessor}
{$M 65500,16384,655360} {Turbo 3 default stack and heap}


{   Program to solve Problem 7.4 in text:                        }
{   POWER GENERATION OPERATION AND CONTROL                       }
{       by Allen J Wood and Bruce F.                             }

program     prob74;


Uses
  Printer;

const
    max_vol_pts : integer = 50;
    max_periods   : integer =  6;
type
    vol_range = 1..50;
    periods_range = 1..6;

var

    inputchar : char;
    printed_output : boolean;

    total_cost_min,
    total_cost_new,
    cost,
    load,
    q, ps, ph,
    vol_step,
    vol_max, vol_min,
    vol_start, vol_end,
    period_length,
    inflow,
    ps_min, ps_max,
    ph_min, ph_max,
    ps_a, ps_b, ps_c
                            : real;

    
    start_state, end_state,
    num_vol_steps, state_i, state_k,
    last_period, jlast, jnow, 
    i, j : integer;

    state_pointer : array[ vol_range, periods_range ] of integer;
    total_cost : array[ vol_range, periods_range ] of real;
    pload : array[ periods_range ] of real;
    ps_sched : array[ vol_range, periods_range ] of real;
    ph_sched : array[ vol_range, periods_range ] of real;
    q_sched : array[ vol_range, periods_range ] of real;
    prod_cost : array[ vol_range, periods_range ] of real;
    Volume : array[ vol_range ] of real;
    Opt_state : array[ periods_range ] of integer;

{------------------------------------------------------------------------}
{ <f> <s> production cost }
procedure pc(     state_i, state_k      : integer;
              var cost, ps, ph, q, load : real       );

    { procedure to calculate the production cost on the equivalent
      steam plant given the reservoir volume transition from
      state_i to state_k.}

var
    vave, ph_max : real;

begin
    vave := ( Volume[state_i] + Volume[state_k] ) / 2.0;
    ph_max := 200.0 * ( 0.9 + vave/1.0E+5 );
    q := ( Volume[state_i] - Volume[state_k] )/period_length + inflow;
    if ( abs( q ) <= 0.05 ) or
       ( q > 260.0        ) then
    begin
        if abs( q ) <= 0.05 then 
        begin
            ph := 0.0;
            q := 0.0;
        end;
        if q > 260.0 then ph := ( q-260.0)/(10.0*(1.1-vave/1.0E+05)) ;
        if ph < ph_min then cost := -1.0 ;
        if ph > ph_max then cost := -1.0 ;
        if ( ph >= ph_min ) and
           ( ph <= ph_max ) then
            begin
                ps := load - ph;
                if ps < ps_min then cost := -1.0 ;
                if ps > ps_max then cost := -1.0 ;
                if ( ps >= ps_min ) and
                   ( ps <= ps_max ) then
                       cost := period_length * ( ps_a + ps_b * ps +
                                          ps_c * ps * ps ) ;
            end;
    end
    else
        cost := -1.0 ;
end;

{------------------------------------------------------------------------}
{ <f> <s> output plant data }
procedure output_plant_data( var outfile:text );

begin
   writeln(outfile);
   writeln(outfile,'  Steam plant maximum MW    = ',ps_max:12:2);
   writeln(outfile,'  Steam plant minimum MW    = ',ps_min:12:2);
   writeln(outfile,'  Reservoir inflow          = ',inflow:12:2);
   writeln(outfile,'  Reservoir maximum volume  = ',vol_max:12:2);
   writeln(outfile,'  Reservoir minimum volume  = ',vol_min:12:2);
   writeln(outfile,'  Volume step size          = ',vol_step:12:2);
   writeln(outfile,'  Reservoir starting volume = ',vol_start:12:2);
   writeln(outfile,'  Reservoir ending volume   = ',vol_end:12:2);
   writeln(outfile);
end; { End procedure }

{----------------------------------------------------------------------------}
{ <f> <s>   numeric value input procedure }
procedure numinput( var value:real );

{This routine handles keyboard input of real numbers}

var
   number_string : string[20];
   code, i, remainder : integer;
   input_string : string[20];
   decimal_found : boolean ;

label terminate;

begin

for i:= 1 to 20 do input_string[i] := ' '; decimal_found := false;

readln( input_string );

{ If the string is zero length the user just hit the enter key, set}
{ the result to 0.0 and return }

if length( input_string ) = 0 then
         begin
         number_string := '0.0';
         goto terminate
         end;

i := 0;        { Find first non blank character }
remainder := length( input_string );
repeat
i := i + 1;
remainder := remainder - 1;
until ( input_string[i] <> ' ') or ( remainder = 0 );

{ If the last character in the string is blank, the field was blank }
{ set the string to 0.0 }

if input_string[i] = ' ' then 
         begin
         number_string := '0.0';
         goto terminate
         end;

{ If remainder = 0 the user entered only one number }

if remainder = 0 then
         begin
         number_string := input_string + '.0';
         goto terminate
         end;

{ Put leading zero on number, behind minus sign if number is neg }

if input_string[i] = '-' then number_string := '-0'
                         else number_string := '0' + input_string[i]; if
input_string[i] = '.' then decimal_found := true;

{ Copy number to number string array }

repeat
i := i + 1;
if input_string[i] <>' ' then
    begin
    number_string := number_string + input_string[i];
    if input_string[i] = '.' then decimal_found := true
    end; 
until i = length( input_string ); 

{ Check on presence of decimal point, if none add one otherwize } { 
append a zero } 

if decimal_found then number_string := number_string + '0' 
                 else number_string := number_string + '.0'; 

terminate:

val( number_string, value, code ); 

end; { End numinput procedure } 

{------------------------------------------------------------------------}
{ <f> <s> data set up}
procedure data_set_up;
begin


        {  set tables to initial values }

for i := 1 to max_vol_pts do
begin
    for j := 1 to max_periods do
    begin
        total_cost[ i, j ] := -1.0 ;
        ps_sched[ i,j ] := 0.0;
        ph_sched[ i,j ] := 0.0;
        q_sched[ i,j ] := 0.0;
        prod_cost[ i,j ] := -1.0;
    end;
end;

    pload[1] := 600.0;
    pload[2] := 1000.0;
    pload[3] := 900.0 ;
    pload[4] := 500.0 ;
    pload[5] := 400.0 ;
    pload[6] := 300.0 ;

    vol_max := 18000.0;
    vol_min := 6000.0;
    vol_start := 10000.0;
    vol_end := 10000.0;
    vol_step := 1000.0;
    period_length := 4.0;
    last_period := 6;
    inflow := 1000.0;
    ps_min := 200.0 ;
    ps_max := 1200.0;
    ph_min := 0.0 ;
    ps_a := 770.0 ;
    ps_b := 5.28 ;
    ps_c := 0.00055 ;

        {  let user change problem data }

write(' Do you want output on printer (Y or N):' );
readln( inputchar );
if (inputchar = 'Y') or ( inputchar = 'y') then printed_output := true
                                           else printed_output := false;
writeln;
writeln(' You may now make changes to the data for the problem ');

  repeat
    writeln;
    writeln(' Menu of options:');
    writeln;
    writeln('1 - Display data');
    writeln('2 - Enter new steam plant max MW ');
    writeln('3 - Enter new steam plant min MW ');
    writeln('4 - Enter new reservoir infow rate (AF/HR)');
    writeln('5 - Enter new reservoir max volume (AF)');
    writeln('6 - Enter new reservoir min vilume (AF)');
    writeln('7 - Enter new volume step to use in algorithm');
    writeln('8 - Enter new starting reservoir volume (AF)' );
    writeln('9 - Enter new ending reservoir volume (AF)' );
    writeln('10 - Run program');
    writeln;
    write('Enter option number >');
    readln(i);
    if i in [1..10] then
      case i of
      1 : output_plant_data(output);

      2 : begin
          writeln(' Current value of steam plant maximum MW = ',ps_max:12:2);
          writeln;write('Enter new value : ');numinput( ps_max );
          end;

      3 : begin
          writeln(' Current value of steam plant minimum MW = ',ps_min:12:2);
          writeln;write('Enter new value : ');numinput( ps_min );
          end;

      4 : begin
          writeln(' Current value of reservoir inflow = ',inflow:12:2);
          writeln;write('Enter new value : ');numinput( inflow );
          end;

      5 : begin
          writeln(' Current value of reservoir maximum volume = ',vol_max:12:2);
          writeln;write('Enter new value : ');numinput( vol_max );
          end;

      6 : begin
          writeln(' Current value of reservoir minimum volume = ',vol_min:12:2);
          writeln;write('Enter new value : ');numinput( vol_min );
          end;

      7 : begin
          writeln(' Current value of volume step size = ',vol_step:12:2);
          writeln;write('Enter new value : ');numinput( vol_step );
          end;

      8 : begin
          writeln(' Current value of reservoir starting volume = '
                                                          ,vol_start:12:2);
          writeln;write('Enter new value : ');numinput( vol_start );
          end;

      9 : begin
          writeln(' Current value of reservoir ending volume = ',vol_end:12:2);
          writeln;write('Enter new value : ');numinput( vol_end );
          end;

      end;
  until (i < 1) or (i >= 10) ;

        {  set up Volume table  }

i := 1;
Volume[ i ] := vol_min;
repeat
    i := i + 1;
    Volume[ i ] := Volume[ i - 1 ] + vol_step;
    if Volume[ i ] = vol_start then start_state := i;
    if Volume[ i ] = vol_end then end_state := i;
until Volume[ i ] + vol_step > vol_max;
num_vol_steps := i;

end;

{------------------------------------------------------------------------}
{ <f> <s> output results}
procedure output_results( var outfile : text );

    { Trace optimum path and print out }

var j:integer;

begin

writeln(outfile);


for j := 1 to last_period do
begin
 writeln(outfile, 'PERIOD ', j );
 writeln(outfile, '            LOAD = ', pload[ j ]:15:2 );
 writeln(outfile, 'STEAM GENERATION = ', ps_sched[ opt_state[ j ], j ]:15:2 );
 writeln(outfile, 'HYDRO GENERATION = ', ph_sched[ opt_state[ j ], j ]:15:2 );
 writeln(outfile, '               Q = ', q_sched[ opt_state[ j ], j ] :15:2 );
 writeln(outfile, 'RESERVOIR VOLUME = ', Volume[ opt_state[ j ] ]:15:2 );  
 writeln(outfile)
end;

writeln(outfile, 'TOTAL PRODUCTION COST FOR SCHEDULE = ', 
           total_cost[ opt_state[ last_period ], last_period ]:15:2 );
end;
{ <f> <s> main program }
{ ------------------------------  Main program ---------------------}
begin



{ set up data for plants and reservoir }

data_set_up;

if printed_output then output_plant_data(lst)
                  else output_plant_data(output);

{   set up total_cost and state_pointer table for first period }

for state_k := 1 to num_vol_steps do
begin
    pc( start_state, state_k, cost, ps, ph, q, pload[1] );
    total_cost[ state_k,1 ] := cost;
    q_sched[ state_k, 1 ] := q;
    ps_sched[ state_k, 1 ] := ps;
    ph_sched[ state_k, 1 ] := ph;
    prod_cost[ state_k, 1 ] := cost;
    state_pointer[ state_k,1 ] := start_state;
end;

{  Time loop }

for jnow := 2 to last_period do
begin
    writeln( ' Now doing period ',jnow );
    jlast := jnow - 1;

        { k loop }

    for state_k := 1 to num_vol_steps do
    begin
        total_cost_min := 1.0e+10;

        { i loop }

        for state_i := 1 to num_vol_steps do
        begin
            if total_cost[ state_i, jlast ] > 0.0 then
            begin
                pc( state_i, state_k, cost, ps, ph, q, pload[ jnow ] );
                if cost > 0.0 then
                begin
                    total_cost_new := total_cost[ state_i, jlast ] + cost;
                    if total_cost_new < total_cost_min then
                    begin
                        total_cost_min := total_cost_new;
                        total_cost[ state_k, jnow ] := total_cost_new;
                        state_pointer[ state_k, jnow ] := state_i;
                        q_sched[ state_k, jnow ] := q;
                        ps_sched[ state_k, jnow ] := ps;
                        ph_sched[ state_k, jnow ] := ph;
                        prod_cost[ state_k, jnow ] := cost;
                    end;
                end;
            end;
        end;
    end;
end;

    { Trace optimum path and store in Opt_state table }

j := last_period;
Opt_state[ last_period ] := end_state;
repeat
    Opt_state[ j - 1 ] := state_pointer[ opt_state[ j ], j ];
    j := j -1
until j = 1;

if printed_output then output_results(lst)
                  else output_results(output);

end.
