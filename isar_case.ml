(*  Copyright 2009 INRIA  *)
Version.add "$Id: isar_case.ml,v 1.4 2009-10-07 14:42:11 doligez Exp $";;

open Printf;;

let print_case_expr n other oc =
  assert (n > 0);
  fprintf oc "CASE c1x -> e1x";
  if n > 1 then for i = 2 to n do
    fprintf oc " [] c%dx -> e%dx" i i;
  done;
  if other then fprintf oc " [] OTHER -> oth";
;;

let print_branch i oc = fprintf oc "c%dx ==> P (e%dx) ==> FALSE" i i;;

let print_branch_other n other oc =
  for i = 1 to n do fprintf oc "~c%dx ==> " i; done;
  if other then fprintf oc "P (oth) ==> ";
  fprintf oc "FALSE";
;;

let print_seq n sep letter oc =
  assert (n > 0);
  fprintf oc "%s1x" letter;
  if n > 1 then for i = 2 to n do
    fprintf oc "%s%s%dx" sep letter i;
  done;
;;

let template = "
  \"!! P @@@c1x e1x c2x e2x... .
    P (CASE @@@c1x -> e1x [] c2x -> e2x...) ==>
@@@
    (c1x ==> P (e1x) ==> FALSE) ==>
    (c2x ==> P (e2x) ==> FALSE) ==>
...
    (...~c2x & ~c1x@@@ & TRUE ==> FALSE) ==>
    FALSE\"
proof -
  fix P @@@c1x e1x c2x e2x...
  assume h: \"P (CASE @@@c1x -> e1x [] c2x -> e2x...)\"
            (is \"P (?cas)\")
@@@
  assume h1: \"c1x ==> P (e1x) ==> FALSE\"
  assume h2: \"c2x ==> P (e2x) ==> FALSE\"
...
  assume hoth: \"...~c2x & ~c1x@@@ & TRUE ==> FALSE\"
  def cs == \"<<@@@c1x, c2x...>>\" (is \"?cs\")
  def es == \"<<@@@e1x, e2x...>>\" (is \"?es\")
  def arms == \"UNION {CaseArm (?cs[i], ?es[i]) : i \\\\in DOMAIN ?cs}\"
              (is \"?arms\")
  def cas == \"?cas\"
  have h0: \"P (cas)\" using h by (fold cas_def)
  def dcs == \"...c2x | c1x@@@\" (is \"?dcs\")
  show FALSE
  proof (rule zenon_em [of \"?dcs\"])
    assume ha: \"~(?dcs)\"
@@@
    have hh1: \"~c1x\" using ha by blast
    have hh2: \"~c2x\" using ha by blast
...
    show FALSE
      using hoth @@@hh1 hh2... by blast
  next
    assume ha: \"?dcs\"
    def scs == \"zenon_seqify (@@@zenon_appseq (zenon_appseq (...
                               <<>>, @@@c1x), c2x)...)\"
               (is \"?scs\")
    def ses == \"zenon_seqify (@@@zenon_appseq (zenon_appseq (...
                               <<>>, @@@e1x), e2x)...)\"
               (is \"?ses\")
    have ha1: \"\\<exists> i \\<in> DOMAIN ?scs : ?scs[i]\"
      using ha zenon_case_seq_empty
      by (simp only: zenon_case_seq_simpl zenon_seqify_empty, blast)
    have ha2: \"\\<exists> i \\<in> DOMAIN ?cs : ?cs[i]\"
      using ha1 by (simp only: zenon_seqify_appseq zenon_seqify_empty)
    have hb: \"\\\\E x : x \\\\in arms\"
      using zenon_case_domain [OF ha2, where es = \"?es\"]
      by (unfold arms_def, blast)
    have hc: \"(CHOOSE x : x \\\\in arms) \\\\in arms\"
      using hb by (unfold Ex_def, auto)
    have hf0: \"?cas \\\\in arms\"
      using hc by (unfold arms_def, fold Case_def)
    have hf3: \"cas \\\\in UNION {CaseArm (?scs[i], ?ses[i])
                                  : i \\\\in DOMAIN ?scs}\"
              (is \"?hf3\")
      using hf0 by (fold cas_def, unfold arms_def,
                    simp only: zenon_seqify_appseq zenon_seqify_empty)
    have hf4: \"Len (?scs) = Len (?ses)\" (is \"?hf4\")
      by (simp only: zenon_case_len_simpl)
    have hf5: \"?hf4 & ?hf3\"
      by (rule conjI [OF hf4 hf3])
    have hf: \"
               ...cas \\\\in CaseArm (c2x, e2x)
             | cas \\\\in CaseArm (c1x, e1x)@@@
             | cas \\\\in UNION {CaseArm (zenon_seqify (<<>>)[i],
                                          zenon_seqify (<<>>)[i])
                                 : i \\\\in DOMAIN zenon_seqify (<<>>)}
             \" (is \"_ | ?gxx\")
      using hf5 by (simp only: zenon_case_union_simpl, blast)
@@@
    have hg1x: \"cas \\\\in CaseArm (c1x, e1x) => FALSE\"
      using h0 h1 by auto
    have hg2x: \"cas \\\\in CaseArm (c2x, e2x) => FALSE\"
      using h0 h2 by auto
...
    from hf
    have hh0: \"?gxx\" ...(is \"_ | ?g1\")
      by (rule zenon_disjE1 [OF _ hg3x])
    then have hh1: \"?g1\" (is \"_ | ?g0\")
      by (rule zenon_disjE1 [OF _ hg2x])
    then have hh0: \"?g0\"@@@[n-1]
      by (rule zenon_disjE1 [OF _ hg1x])
    have hi: \"cas \\\\in UNION {CaseArm (<<>>[i], <<>>[i])
                                 : i \\\\in DOMAIN <<>>}\"
      using hh0 by (simp only: zenon_seqify_empty)
    show FALSE
      by (rule zenon_case_empty_union [OF hi])
  qed
qed
";;

let template_other = "
  \"!! P oth @@@c1x e1x c2x e2x... .
    P (CASE @@@c1x -> e1x [] c2x -> e2x... [] OTHER -> oth) ==>
@@@
    (c1x ==> P (e1x) ==> FALSE) ==>
    (c2x ==> P (e2x) ==> FALSE) ==>
...
    (...~c2x & ~c1x@@@ & TRUE ==> P (oth) ==> FALSE) ==>
    FALSE\"
proof -
  fix P oth @@@c1x e1x c2x e2x...
  assume h: \"P (CASE @@@c1x -> e1x [] c2x -> e2x... [] OTHER -> oth)\"
            (is \"P (?cas)\")
@@@
  assume h1: \"c1x ==> P (e1x) ==> FALSE\"
  assume h2: \"c2x ==> P (e2x) ==> FALSE\"
...
  assume hoth: \"...~c2x & ~c1x@@@ & TRUE ==> P (oth) ==> FALSE\"
  def cs == \"<<@@@c1x, c2x...>>\" (is \"?cs\")
  def es == \"<<@@@e1x, e2x...>>\" (is \"?es\")
  def arms == \"UNION {CaseArm (?cs[i], ?es[i]) : i \\\\in DOMAIN ?cs}\"
              (is \"?arms\")
  def cas == \"?cas\"
  have h0: \"P (cas)\" using h by (fold cas_def)
  def dcs == \"...c2x | c1x@@@ | FALSE\" (is \"?dcs\")
  def scs == \"zenon_seqify (@@@zenon_appseq (zenon_appseq (...
                             <<>>, @@@c1x), c2x)...)\"
             (is \"?scs\")
  have hscs : \"?cs = ?scs\"
    by (simp only: zenon_seqify_appseq zenon_seqify_empty)
  def ses == \"zenon_seqify (@@@zenon_appseq (zenon_appseq (...
                             <<>>, @@@e1x), e2x)...)\"
             (is \"?ses\")
  have hses : \"?es = ?ses\"
    by (simp only: zenon_seqify_appseq zenon_seqify_empty)
  have hlen: \"Len (?scs) = Len (?ses)\" (is \"?hlen\")
    by (simp only: zenon_case_len_simpl)
  def armoth == \"CaseArm (\\<forall> i \\<in> DOMAIN ?cs : ~?cs[i], oth)\"
                (is \"?armoth\")
  show FALSE
  proof (rule zenon_em [of \"?dcs\"])
    assume ha: \"~(?dcs)\"
    have hb: \"P (CHOOSE x : x \\\\in arms \\<union> armoth)\"
      using h by (unfold CaseOther_def, fold arms_def armoth_def)
    have hc: \"arms \\\\cup armoth
              = UNION {CaseArm (?scs[i], ?ses[i]) : i \\\\in DOMAIN ?scs}
                \\\\cup CaseArm (\\<forall> i \\<in> DOMAIN ?scs : ~?scs[i],
                                 oth)\"
             (is \"_ = ?sarmsoth\")
      using hscs hses by (unfold arms_def armoth_def, auto)
    have hd: \"~(?dcs) & ?hlen & arms \\<union> armoth = ?sarmsoth\"
      using ha hlen hc by blast
    have he: \"arms \\<union> armoth = {oth}\"
      using hd by (simp only: zenon_case_oth_simpl zenon_case_oth_empty)
    have hf: \"(CHOOSE x : x \\\\in arms \\\\cup armoth) = oth\"
      using he by auto
    have hg: \"P (oth)\"
      using hb hf by auto
@@@
    have hh1: \"~c1x\" using ha by blast
    have hh2: \"~c2x\" using ha by blast
...
    show FALSE
      using hg hoth @@@hh1 hh2... by blast
  next
    assume ha: \"?dcs\"
    have ha1: \"\\<exists> i \\<in> DOMAIN ?scs : ?scs[i]\"
      using ha zenon_case_seq_empty
      by (simp only: zenon_case_seq_simpl zenon_seqify_empty, blast)
    have ha2: \"\\<exists> i \\<in> DOMAIN ?cs : ?cs[i]\"
      using ha1 hscs by auto
    have ha3: \"~ (\\<forall> i \\<in> DOMAIN ?cs : ~?cs[i])\"
      using ha2 by blast
    have ha4: \"armoth = {}\"
      using ha3 condElse [OF ha3, where t = \"{oth}\" and e = \"{}\"]
      by (unfold armoth_def CaseArm_def, blast)
    have hb: \"\\\\E x : x \\\\in arms \\\\cup armoth\"
      using zenon_case_domain [OF ha2, where es = \"?es\"]
      by (unfold arms_def, blast)
    have hc: \"(CHOOSE x : x \\\\in arms \\\\cup armoth)
               \\\\in arms \\\\cup armoth\"
      using hb by (unfold Ex_def, auto)
    have hf0: \"?cas \\\\in arms \\\\cup armoth\"
      using hc by (unfold arms_def armoth_def, fold CaseOther_def)
    have hf1: \"cas \\\\in arms \\\\cup armoth\"
      using hf0 by (fold cas_def)
    have hf2: \"cas \\\\in arms\"
      using hf1 ha4 by auto
    have hf3: \"cas \\\\in UNION {CaseArm (?scs[i], ?ses[i])
                                  : i \\\\in DOMAIN ?scs}\"
              (is \"?hf3\")
      using hf2 by (unfold arms_def,
                    simp only: zenon_seqify_appseq zenon_seqify_empty)
    have hf5: \"?hlen & ?hf3\"
      by (rule conjI [OF hlen hf3])
    have hf: \"
               ...cas \\\\in CaseArm (c2x, e2x)
             | cas \\\\in CaseArm (c1x, e1x)@@@
             | cas \\\\in UNION {CaseArm (zenon_seqify (<<>>)[i],
                                          zenon_seqify (<<>>)[i])
                                 : i \\\\in DOMAIN zenon_seqify (<<>>)}
             \" (is \"_ | ?gxx\")
      using hf5 by (simp only: zenon_case_union_simpl, blast)
@@@
    have hg1x: \"cas \\\\in CaseArm (c1x, e1x) => FALSE\"
      using h0 h1 by auto
    have hg2x: \"cas \\\\in CaseArm (c2x, e2x) => FALSE\"
      using h0 h2 by auto
...
    from hf
    have hh0: \"?gxx\" ...(is \"_ | ?g1\")
      by (rule zenon_disjE1 [OF _ hg3x])
    then have hh1: \"?g1\" (is \"_ | ?g0\")
      by (rule zenon_disjE1 [OF _ hg2x])
    then have hh0: \"?g0\"@@@[n-1]
      by (rule zenon_disjE1 [OF _ hg1x])
    have hi: \"cas \\\\in UNION {CaseArm (<<>>[i], <<>>[i])
                                 : i \\\\in DOMAIN <<>>}\"
      using hh0 by (simp only: zenon_seqify_empty)
    show FALSE
      by (rule zenon_case_empty_union [OF hi])
  qed
qed
";;

let print_case kind n other oc =
  assert (n > 0);
  fprintf oc "%s zenon_case%s%d :" kind (if other then "other" else "") n;
  let tpl = if other then template_other else template in
  output_string oc (Enum.expand_text n tpl);
;;

let print_up_to n file =
  let oc = open_out file in
  for i = 1 to n do
    print_case "lemma" i false oc;
    fprintf oc "\n";
    print_case "lemma" i true oc;
    fprintf oc "\n";
  done;
  close_out oc;
;;

let test_case n other =
  let oc = open_out "/tmp/testcase.thy" in
  fprintf oc "theory testcase\n";
  fprintf oc "imports Zenon\n";
  fprintf oc "begin\n\n";
  print_case "lemma" n other oc;
  fprintf oc "end\n";
  close_out oc;
  fprintf stderr "Now run:\n";
  fprintf stderr "time isabelle-process -r \
                       -e \"(use_thy \\\"/tmp/testcase\\\"; \
                             OS.Process.exit OS.Process.success);\" TLA+\n";
  flush stderr;
;;
