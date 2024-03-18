{
module Tokenizer where
}

%wrapper "basic"

$digit = 0-9
$alphabetlittle = [a-z]
$alphabetbig = [A-Z]

:-
  $white+ 						;
  \(      						{\a -> ST_LPAR}
  \!      						{\a -> ST_Not}
  \|      						{\a -> ST_Or}
  \&      						{\a -> ST_And}
  "->"    						{\a -> ST_Con}
  \@    						{\a -> ST_All}
  \?    						{\a -> ST_One}
  $alphabetlittle [$alphabetlittle $digit]* 	{\a -> ST_Var a}
  $alphabetbig [$alphabetbig $digit]* 	{\a -> ST_Pred a}
  \)      						{\a -> ST_RPAR}
  \,                            {\a -> ST_Next}
  \.                            {\a -> ST_Point}

{
data StatToken
  = ST_Var String
  | ST_Pred String
  | ST_All
  | ST_One
  | ST_Not
  | ST_And
  | ST_Or
  | ST_Con
  | ST_LPAR
  | ST_RPAR
  | ST_Next
  | ST_Point
}