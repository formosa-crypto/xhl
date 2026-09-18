(* -------------------------------------------------------------------- *)
Reserved Notation "'If' e 'then' c1 'else' c2"
  (at level 65, right associativity, format
     "'[hv   ' 'If'  e  '/' '[v' 'then'  c1  ']' '/' '[v' 'else'  c2 ']' ']'").

Reserved Notation "'IfT' e 'then' c1"
  (at level 65, right associativity, format
     "'[hv   ' 'IfT'  e  '/' '[v' 'then'  c1 ']' ']'").

Reserved Notation "'While' e 'Do' c"
  (at level 65, no associativity, format
     "'[v  ' 'While'  e  'Do'  '/' c ']'").

Reserved Notation "x <<- e"
  (at level 65, e at level 70, no associativity, format "x  <<-  e").

Reserved Notation "x <$- d"
  (at level 65, d at level 70, no associativity, format "x  <$-  d").

Reserved Notation "` x"
  (at level 1, format "` x").

Reserved Notation "c1 ;; c2"
  (at level 74, left associativity, format "'[v' c1  ;; '/' c2 ']'").

(* -------------------------------------------------------------------- *)
Reserved Notation "<< >>"
  (at level 0, format "<< >>").

Reserved Notation "<< i >>"
  (at level 0, format "<<  i  >>").

Reserved Notation "<< x1 ; x2 ; .. ; xn >>"
  (at level 0, format "<< '[v'  x1 ; '/'  x2 ; '/'  .. ; '/'  xn ']' '/'  >>").
