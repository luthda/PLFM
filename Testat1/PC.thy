(*  Title:      PC.thy
    Author:     Farhad Mehta
*)

chapter \<open>Propositional Calculus\<close>

text \<open>
The main aim of this theory is for the user to be able to perform (simulated) sequent style proofs in the logics basicPC and PC within Isabelle/HOL.

This theory does not claim to be comprehensive, particularly elegant, or some form of 'best practice', but should rather allow you to get a quick first experience of working with an industry-strength proof assistant.

This theory file is made to be looked at within an interactive Isabelle/jEdit proving session.
\<close>

theory PC
imports Main
begin

text \<open>
What follows is a demonstration of some Isabelle/HOL syntax as well as Isabelle/HOL theorems containing (meta) implications (corresponding to proof rule schemas) and equalities (corresponding to syntactic definitions) that can be used to simulate sequent calculus style proofs in the logics basicPC and PC. How this is possible will be clearer when looking at the example proofs of concrete sequents.

Although one could have just introduced these rule schemas as axioms, proving them from the Isabelle/HOL definitions serves as a sanity check to make sure that they are indeed correct.

Since the syntax and proof rules for propositional calculus are already defined in Isabelle/HOL, most of the theorems below are renamed versions of theorems that already exist in Isabelle/HOL. 

The syntax and syntax conventions of Isabelle/HOL are somewhat different compared to what we have considered till now, but it is similar enough to be understood without much further explanation.

The structure of this theory roughly corresponds to the structure of the related chapter in the lecture notes.
\<close>

section \<open>Syntax of Sequents\<close>

term "\<lbrakk> Hyp1 ; Hyp2 ; Hyp3 \<rbrakk> \<Longrightarrow> Goal"

text \<open> or equivalently \<close>

term " Hyp1 \<Longrightarrow> Hyp2 \<Longrightarrow> Hyp3 \<Longrightarrow> Goal"

text \<open>
The directive 'term' displays the type of a term in the "Output" pane.
In this theory file, it is used merely to display syntax examples.
\<close>

section \<open>Syntax of basicPC\<close>

term "False"
term "\<not> P"
term "P \<and> P"


section \<open>Proof Rules of basicPC\<close>

theorem hyp:"P \<Longrightarrow> P"
  by assumption

theorem mon:"\<lbrakk> P ; Q \<rbrakk> \<Longrightarrow> Q"
  by assumption

theorem cut:"\<lbrakk> P ; P \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by assumption

theorem false_hyp:"False \<Longrightarrow> P"
  by (erule FalseE)

theorem contr:"\<lbrakk> \<not>P \<Longrightarrow> False \<rbrakk>\<Longrightarrow> P"
  by (rule ccontr)

theorem not_goal:"\<lbrakk> P \<Longrightarrow> False \<rbrakk>\<Longrightarrow> \<not>P"
  by (rule notI)

theorem not_hyp:"\<lbrakk> \<not>P ; P \<rbrakk>\<Longrightarrow> Q"
  by (erule notE)

theorem and_goal:"\<lbrakk> P ; Q \<rbrakk>\<Longrightarrow> P \<and> Q"
  by (rule conjI)

theorem and_hyp:"\<lbrakk> P \<and> Q ; \<lbrakk> P ; Q\<rbrakk> \<Longrightarrow> R \<rbrakk>\<Longrightarrow> R"
  by (erule conjE)


subsection \<open>Examples of basicPC Proofs\<close>

text \<open>
What follows are some examples of concrete proofs in basicPC.

Note that:
- You are only allowed to use the theorems defined and proved above.
- The rules with the suffix 'hyp' are in the form of so-called 'elimination' rules and need to be invoked using the tactic 'erule' in the following way: apply (erule <rule_name>).
- The rest of the rules are in the form of so-called 'introduction' rules and need to be invoked using the tactic 'rule' in the following way: apply (rule <rule_name>).
- Use the tactic 'assumption' in place of the rule hyp.
- Most meta variables within the proof rule schemas will be instantiated automatically via unification. This can also be done manually if needed (for instance when using the cut rule), using the following syntax: cut[where ?P = "A" and ?Q = "B"]

In case you are feeling lazy, or would like to check if what your proving is actually valid, you may try the proof tactic 'auto', which performs a mixture of logical and equational reasoning that should be adequate for most proofs in this chapter, using the following command: apply auto
\<close>

text \<open>
The directive 'thm' displays the content of a theorem in the "Output" pane.
\<close>
thm cut
thm cut[where ?P = "A" and ?Q = "B"]

lemma "A \<and> B \<Longrightarrow> B \<and> A"
  apply (erule and_hyp)
  apply (rule and_goal)
   apply assumption
  apply assumption
  done

text \<open>
Same proof as above, with explicit instantiation of meta variables.
\<close>


lemma "A \<and> B \<Longrightarrow> B \<and> A"
  apply (erule and_hyp[where ?R = "B \<and> A" and ?P="A" and ?Q="B"])
  apply (rule and_goal[where ?P="B" and ?Q="A"])
   apply assumption
  apply assumption
  done

text \<open>
And if one is feeling lazy, or is unsure if what one is trying to prove is actually valid...
\<close>


lemma "A \<and> B \<Longrightarrow> B \<and> A"
  by auto

lemma "B \<Longrightarrow> B \<and> A"
  apply auto
  nitpick
  oops

section \<open>Derived Logical Operators\<close>

theorem true_def:"True = (\<not> False)"
  by (simp only: not_False_eq_True)

theorem or_def:"(P \<or> Q) = (\<not> ( \<not>P \<and> \<not>Q ))"
  by simp

theorem imp_def:"(P \<longrightarrow> Q) = (\<not>P \<or> Q)"
  by simp

theorem eqv_def:"(P \<longleftrightarrow> Q) = ((P \<longrightarrow> Q) \<and> (Q \<longrightarrow> P))"
  by auto


text \<open>
Helper lemmas to make unfolding definitions within goals and hypotheses easier.
\<close>
lemma unfold_def_goal:"\<lbrakk> t = s ; P s \<rbrakk> \<Longrightarrow> P t"
  by (erule ssubst)

lemma unfold_def_hyp:"\<lbrakk> t = s ; P t ; P s \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by auto

thm unfold_def_goal [OF or_def]
thm unfold_def_hyp [OF or_def]

theorem true_goal:"True"
  apply (rule unfold_def_goal [OF true_def])
  apply (rule not_goal)
  apply assumption
  done

theorem or_goal1:"P \<Longrightarrow> P \<or> Q"
  apply (rule unfold_def_goal [OF or_def])
  apply (rule not_goal)
  apply (erule and_hyp)
  apply (erule not_hyp [where ?P="P"])
  apply assumption
  done

theorem or_goal2:"Q \<Longrightarrow> P \<or> Q"
  apply (rule unfold_def_goal [OF or_def])
  apply (rule not_goal)
  apply (erule and_hyp)
  apply (erule not_hyp [where ?P="Q"])
  apply assumption
  done


theorem or_hyp:"\<lbrakk> P \<or> Q ; P \<Longrightarrow> R ; Q \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  apply (erule unfold_def_hyp [OF or_def])
  apply (rule contr)
  apply (erule not_hyp[where ?P="(\<not> P \<and> \<not> Q)"])
  apply (rule and_goal)
   apply (rule not_goal)
   apply (erule not_hyp[where ?P="R"])
   apply assumption
   apply (rule not_goal)
   apply (erule not_hyp[where ?P="R"])
  apply assumption
  done

(* TODO: Replace the "by auto" proofs with step by step proofs using the definition unfolding and the basicPC rules *)

theorem imp_goal:"\<lbrakk> P \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> P \<longrightarrow> Q"
  by auto


theorem imp_hyp:"\<lbrakk> P \<longrightarrow> Q ; P ; Q \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by auto

theorem eqv_goal:"\<lbrakk> P \<Longrightarrow> Q ; Q \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P \<longleftrightarrow> Q"
  by auto

theorem eq_hyp:"\<lbrakk> P \<longleftrightarrow> Q ; \<lbrakk> P \<longrightarrow> Q ;  Q \<longrightarrow> P \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by auto


section \<open>Exercises\<close>


lemma Ex_2_2_1:"\<lbrakk> R \<longrightarrow> C ; R \<rbrakk> \<Longrightarrow> C"
  oops

lemma Ex_2_3_1:"\<not>\<not> False \<Longrightarrow> False"
  apply (rule contr)
  apply (erule not_hyp)
  by (rule hyp)

(* TODO: Complete the other proving exercises from the lecture notes *)


lemma Testat_Exercise_1:"(A \<longrightarrow> A)"
  apply (rule imp_goal)
  apply assumption
  done

lemma Testat_Exercise_2:"(B \<longrightarrow> C) \<longrightarrow> ( (A \<longrightarrow> B) \<longrightarrow> (A \<longrightarrow> C))"
  apply (rule imp_goal)
  apply (rule imp_goal)
  apply (rule imp_goal)
  apply (erule imp_hyp [where ?P="A" and ?Q="B"])
   apply assumption
  apply (erule imp_hyp [where ?P="B" and ?Q="C"])
   apply assumption
  apply assumption
  done

  (* Hint: Be sure to first go through the contents of this theory file from the beginning, and pay special attention to the text in the beginning of the subsection "Examples of basicPC Proofs" with the points describing the structure of each line within a proof script. Trying to complete this proof without this basic information will be a frustrating experience. *)
  (* Hint: The rest of the proof only contains steps that have already been done above above, albeit with a different instantiation. Clicking on the individual "apply" lines above within the Isabelle IDE will show you the proof state at that line on the frame to the right.*)

end