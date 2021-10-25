theory tp5bis
  imports Main 
begin

(* les glob sont les chaînes unix qui utilisent les jokers ?, * et + pour décrire des ensembles de noms *)

(* Définition du type glob (ici nommé pattern) *)
datatype symbol = Char char | Star | Qmark | Plus

type_synonym word= "char list"
type_synonym pattern= "symbol list" 

(* La fonction qui dit si un mot est accepté par un pattern/glob  *)
fun accept::"pattern \<Rightarrow> word \<Rightarrow> bool"
  where
"accept [] [] = True" |
"accept [Star] _ = True" |
"accept [] (_#_) = False" |
"accept ((Char x)#_) [] = False" | 
"accept ((Char x)#r1) (y#r2) = (if x=y then (accept r1 r2) else False)"  |
"accept (Qmark#r1) [] = False" |
"accept (Qmark#r1) (_#r2) = (accept r1 r2)" |
"accept (Plus#r1) [] = False" |
"accept (Plus#r1) (a#r2) = (accept (Star#r1) r2)" |
"accept (Star#r1) [] = (accept r1 [])" |
"accept (Star#r1) (a#r2) = ((accept r1 (a#r2)) \<or> (accept r1 r2) \<or> (accept (Star#r1) r2))"

(* Les caractères en Isabelle/HOL *)
value "(CHR ''a'')"

(* Quelques exemples d'utilisation de la fonction accept *)
value "accept [Star,(Char (CHR ''a''))] [(CHR ''a'')]"
value "accept [Star,(Char (CHR ''a''))] [(CHR ''b''),(CHR ''a'')]"
value "accept [Star,(Char (CHR ''a''))] [(CHR ''a''),(CHR ''b'')]"
value "accept [Star,Star] []"
value "accept [Plus,Star,Star] []"


(* ----------------------------- Votre TP commence ici! ---------------------------------------- *)
fun simplify::"pattern \<Rightarrow> pattern"
  where
"simplify [] = []" |
"simplify [h1] = [h1]" |
"simplify (Qmark#Star#q) = simplify(Plus#q)"|
"simplify (Star#Qmark#q) = simplify(Plus#q)"|
"simplify (Star#Plus#q) = simplify(Plus#q)"|
"simplify (Plus#Star#q) = simplify(Plus#q)"|
"simplify (Star#Star#q) = simplify(Star#q)"|
"simplify (Plus#Plus#q) = Qmark#(simplify(Plus#q))"|
"simplify (Plus#Qmark#q) = Qmark#(simplify(Plus#q))"|
"simplify (h1#h2#q) = h1#(simplify(h2#q))"


(* Le lemme de correction de la fonction simplify... Pour le prouver voir les lemmes intermédiaires à définir, plus bas. *)
lemma "(accept glob word) = (accept (simplify glob) word)"
  nitpick
  quickcheck [tester=narrowing]
  oops


(* Le lemme de minimalité dit que le pattern simplifié est le plus petit de tous les
   patterns équivalents. Reformulé ici sous la forme de sa contraposée: s'il existe un pattern 
   plus petit que le pattern simplifié alors il n'est pas équivalent. 
   Il n'est pas équivalent si il existe au moins un mot pour lequel l'acceptation par 
   "accept" sera différente. *)

lemma "((length p)< (length (simplify p2))) \<longrightarrow> (\<exists> w. (accept p w) \<noteq> (accept (simplify p2) w))"
 (* La preuve de ce lemme n'est pas demandée. *)
 (* Utiliser le lemme suivant pour trouver des contre-exemples *)
  oops

(* Pour trouver (efficacement) des contre-exemples sur ce lemme de minimalité, on va limiter 
   la complexité des patterns considérés qu'on nommera "basicPattern" : Ici des patterns 
    avec *, ?, + et uniquement le caractère A *)


fun basicPattern:: "pattern \<Rightarrow> bool"
  where
"basicPattern [] = True" |
"basicPattern ((Char CHR ''A'') # r) = basicPattern r" |
"basicPattern ((Char _) # r) = False" |
"basicPattern (_ # r) = basicPattern r"

(* Le lemme de minimalité pour les basicPatterns *)
lemma "(basicPattern p) \<longrightarrow> ((length p)< (length (simplify p2))) \<longrightarrow> (\<exists> w. (accept p w) \<noteq> (accept (simplify p2) w))"
  quickcheck [tester=narrowing,timeout=00]
   (* nitpick ne trouve que des contre-exemples qui n'en sont pas *)
  oops

(* La directive d'export du code Scala *)
(* A ne pas modifier! *)
code_reserved Scala
  symbol 
code_printing
   type_constructor symbol \<rightharpoonup> (Scala) "Symbol"
   | constant Char \<rightharpoonup> (Scala) "Char"
   | constant Star \<rightharpoonup> (Scala) "Star"
   | constant Plus \<rightharpoonup> (Scala) "Plus"
   | constant Qmark \<rightharpoonup> (Scala) "Qmark"

export_code simplify in Scala


(* Pour prouver le lemme de correction, il vous sera nécessaire de prouver tous ces lemmes intermédiaires! *)

(* Le pattern vide n'accepte que le mot vide *)
lemma acceptVide: "(accept [] w) \<longrightarrow> w=[]"
  apply (case_tac w)
   apply simp
  apply simp
  done


lemma acceptVide2_aux: "((accept p w) \<and> (w \<noteq> [])) \<longrightarrow> (p \<noteq> [])"
  apply (case_tac w)
   apply simp
  apply (case_tac p)
   apply simp
  apply simp
  done

(* Le seul pattern n'acceptant que le mot vide est le pattern vide *)
lemma acceptVide2: "(\<forall> w. w\<noteq>[] \<longrightarrow> \<not>(accept p w)) \<longrightarrow> p=[]"
  apply (induct p)
   apply simp
  apply (case_tac a)
     apply auto
     prefer 3
     apply (case_tac "([CHR ''a''] \<noteq> []) \<and> (accept [Qmark] [CHR ''a''])")
      apply blast
     apply simp
    apply (case_tac "([x1] \<noteq> []) \<and> (accept [Char x1] [x1])")
     apply blast
    apply simp
   apply (metis accept.simps(11) acceptVide2_aux list.exhaust)
  apply (metis accept.simps(11) accept.simps(9) acceptVide2_aux list.exhaust list.simps(3))
  done

(* Le seul pattern n'acceptant que le langage ? est ? *)
lemma acceptQmark: "(\<forall> w. (accept [Qmark] w = (accept p w))) \<longrightarrow> p=[Qmark]"
  apply (induct p)
  using accept.simps(1) accept.simps(6) apply blast
  apply (case_tac "accept [Qmark] (x1#x2#[]) = accept (a#p)(x1#x2#[])")
   prefer 2
   apply blast
  apply (case_tac "accept [Qmark] (x1#x2#[])")
   apply simp
  apply (case_tac a)
     apply (metis (mono_tags, hide_lams) accept.simps(1) accept.simps(5) accept.simps(7) basicPattern.simps(1) basicPattern.simps(2) basicPattern.simps(8))
    apply (metis (full_types) accept.simps(11) accept.simps(2) accept.simps(7) acceptVide acceptVide2 neq_Nil_conv)
   apply (metis accept.simps(7) acceptVide acceptVide2)
  by (metis (full_types) accept.simps(7) accept.simps(9) acceptVide acceptVide2 list.distinct(1))

(* Si le pattern commence par un caractère ou un point d'interrogation alors le mot accepté
   commence forcément par un caractère (il ne peut être vide) *)
lemma charAndQmarkRemoval: "((x\<noteq>Star) \<and> (x\<noteq> Plus) \<and> (accept (x#r) m)) \<longrightarrow> (\<exists> x2 r2. m=x2#r2 \<and> (accept r r2))"
  apply (case_tac m)
   apply (case_tac[1-] x)
         apply simp
        apply simp
       apply simp
      apply simp
     apply simp
    apply simp
   apply simp
  apply simp
  done

  
(* Si le pattern commence par une étoile, on peut soit l'oublier soit oublier le premier caractère du mot accepté *)
lemma patternStartsWithStar: "((accept (Star#r) m)) \<longrightarrow> ((accept r m) \<or> (\<exists> x2 r2. m=x2#r2 \<and> (accept (Star#r) r2)))"
  apply (case_tac m)
   apply simp
   apply (case_tac r)
    apply simp
   apply simp
  apply auto
  apply (case_tac "accept r (a # list)")
   apply simp
  apply (case_tac "accept (Star # r) list")
   apply simp
  apply auto
  by (metis accept.simps(10) accept.simps(11) accept.simps(2) neq_Nil_conv)
    
(* On peut compléter à gauche n'importe quel pattern par une étoile *)
lemma completePatternWithStar: "(accept r m) \<longrightarrow> (accept (Star#r) m)"
  apply (case_tac r)
   apply simp
  by (metis (full_types) accept.simps(10) accept.simps(11) list.exhaust)

lemma completePatternWithStar2: "(accept r m) \<longrightarrow> (accept (Star#r) (m1@m))"
  apply (case_tac "accept [Star] m1")
   apply auto
  apply (induct m1)
   apply simp
  using completePatternWithStar
   apply simp
  by (metis (full_types) accept.simps(11) accept.simps(2) append_Cons neq_Nil_conv)

(* On peut oublier une étoile dès qu'il y en a une juste après *)
lemma forgetOneStar:"(accept (Star#(Star#r)) w) = (accept (Star#r) w)"
  apply (induct w)
   apply simp
  by (metis (full_types) accept.simps(1) accept.simps(11) append_Nil2 completePatternWithStar2 list.exhaust)

(* Etoile suivie de point d'interrogation est équivalent à point d'interrogation étoile *)
lemma starQmark:"((accept (Star#(Qmark#r)) w) = (accept (Qmark#(Star#r)) w))"
  apply (induct w)
   apply simp
  using charAndQmarkRemoval
  using completePatternWithStar
  using forgetOneStar
  using patternStartsWithStar
  apply fastforce
  done
  
(* Si deux patterns sont équivalents on peut les compléter à gauche... *)

(* ... par une étoile *)
lemma equivalentPatternStar:"((\<forall> w1. (accept p1 w1) = (accept p2 w1))) \<longrightarrow> ((accept (Star#p1) w) = (accept (Star#p2) w))"
  apply (induct w)
  using completePatternWithStar
  using patternStartsWithStar
   apply blast
  by (smt accept.simps(11) completePatternWithStar forgetOneStar list.sel(3) patternStartsWithStar)

(* ... par un caractère (identique) *)
lemma equivalentPatternChar:"((\<forall> w. (accept p1 w) = (accept p2 w))) \<longrightarrow> ((accept ((Char x)#p1) w) = (accept ((Char x)#p2) w))"
  apply (induct w)
   apply simp
  apply simp
  done

(* ... par un point d'interrogation *)
lemma equivalentPatternQmark:"((\<forall> w. (accept p1 w) = (accept p2 w))) \<longrightarrow> ((accept (Qmark#p1) w) = (accept (Qmark#p2) w))"
  apply (induct w)
   apply simp
  apply simp
  done
  
(* Par un plus *)
lemma equivalentPatternPlus:"((\<forall> w. (accept p1 w) = (accept p2 w))) \<longrightarrow> ((accept (Plus#p1) w) = (accept (Plus#p2) w))"
  apply (induct w)
   apply simp
  using equivalentPatternStar
  apply simp
  done  
  
lemma plusStarQmark:"((accept (Star#(Qmark#r)) w) = (accept (Plus#r) w))"
  apply (induct w)
   apply simp
  using accept.simps(7) accept.simps(9) starQmark by blast
  

lemma plusStarStar:"((accept (Plus#(Star#r)) w) = (accept (Plus#r) w))"
  apply (induct w)
   apply simp
  using forgetOneStar
  apply simp
  done
  

lemma plusPlus1:"((accept (Plus#(Plus#r)) w) = (accept (Qmark#(Plus#r)) w))"
  apply (induct w)
   apply simp
  by (metis (full_types) accept.simps(11) accept.simps(7) accept.simps(9) patternStartsWithStar plusStarQmark)
  

lemma correction_direct:"(accept glob word) \<longrightarrow> (accept (simplify glob) word)"
  apply (induct glob)
   apply simp
  apply (case_tac a)
     apply (induct word)
      apply simp

      
  

(*
  apply (induct word)
   apply (induct glob)
    apply simp
   apply (case_tac a)
      apply simp
     prefer 2
     apply simp
    prefer 2
    using accept.simps(8) apply blast
     apply simp
     apply (metis charAndQmarkRemoval neq_Nil_conv patternStartsWithStar simplify.simps(2) simplify.simps(5) simplify.simps(7))
    apply (case_tac glob)
     apply simp
    apply (case_tac aa)
       apply (case_tac "a = x1")
    prefer 2
        apply simp
*)


    
    




(* Le lemme de correction final *)
lemma correction:"(accept glob word) = (accept (simplify glob) word)"
(*  using acceptVide acceptVide2 acceptQmark charAndQmarkRemoval patternStartsWithStar completePatternWithStar completePatternWithStar2 forgetOneStar starQmark equivalentPatternStar equivalentPatternQmark equivalentPatternPlus equivalentPatternChar plusStarQmark plusStarStar plusPlus1 *)
  apply (induct word)
   apply (case_tac glob)
    apply simp
   apply (case_tac a)
      apply (metis (full_types) accept.simps(4) list.exhaust simplify.simps(10) simplify.simps(2))
     apply auto
  oops


  

  
end
 