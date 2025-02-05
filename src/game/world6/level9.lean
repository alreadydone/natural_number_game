/-
# Proposition world. 

## Level 9 : a big maze. 

Lean's "congruence closure" tactic `cc` is good at mazes. Perhaps I should have
mentioned it earlier.
-/

/- Lemma : no-side-bar
There is a way through the following maze.
-/
example (A B C D E F G H I J K L : Prop)
(f1 : A → B) (f2 : B → E) (f3 : E → D) (f4 : D → A) (f5 : E → F)
(f6 : F → C) (f7 : B → C) (f8 : F → G) (f9 : G → J) (f10 : I → J)
(f11 : J → I) (f12 : I → H) (f13 : E → H) (f14 : H → K) (f15 : I → L)
 : A → L :=
begin
  cc,



end

/-
Still to come in proposition world: `∧`! `∨`! `↔`! `∃`! And
the tactics `cases`, `split`, `left`, `right`, `use`. 
But the good news is that (1) all these tactics are easy and (2)
they will be the last tactics you will need to know
in order to become a competent Lean user. Indeed, after working through
the rest of proposition world (which KB hasn't written yet) you
should have all the tools you need to solve all the levels in advanced
addition world, advanced multiplication world, and the 30 levels of
inequality world.

-/
