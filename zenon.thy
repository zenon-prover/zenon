theory zenon
imports HOL

begin

lemma zenon_nnpp: "(~P ==> False) ==> P"
by blast

lemma zenon_nppf: "~P ==> P ==> False"
by blast

lemma zenon_eqrefl: "t = t"
by auto


lemma zenon_nottrue: "~True ==> False"
by blast

lemma zenon_noteq: "~x=x ==> False"
by blast

lemma zenon_and: "P & Q ==> (P ==> Q ==> False) ==> False"
by blast

lemma zenon_or: "P | Q ==> (P ==> False) ==> (Q ==> False) ==> False"
by blast

lemma zenon_imply: "P --> Q ==> (~P ==> False) ==> (Q ==> False) ==> False"
by blast

lemma zenon_equiv:
  "P <-> Q ==> (~P ==> ~Q ==> False) ==> (P ==> Q ==> False) ==> False"
by blast

lemma zenon_notnot: "~~P ==> (P ==> False) ==> False"
by blast

lemma zenon_notand: "~(P & Q) ==> (~P ==> False) ==> (~Q ==> False) ==> False"
by blast

lemma zenon_notor: "~(P | Q) ==> (~P ==> ~Q ==> False) ==> False"
by blast

lemma zenon_notimply: "~(A-->B) ==> (A ==> ~B ==> False) ==> False"
by blast

lemma zenon_notequiv:
  "~(P <-> Q) ==> (~P ==> Q ==> False) ==> (P ==> ~Q ==> False) ==> False"
by blast

lemma zenon_ex: "EX x. P x ==> (!!x. P x ==> False) ==> False"
by blast

lemma zenon_all: "ALL x. P x ==> (P t ==> False) ==> False"
by blast

lemma zenon_notex: "~(EX x. P x) ==> (~P t ==> False) ==> False"
by blast

lemma zenon_notall: "~(ALL x. P x) ==> (!!x. ~P x ==> False) ==> False"
by blast

end
