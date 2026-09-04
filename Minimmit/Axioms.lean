import Minimmit.Analysis.Consistency.Lemma5_1
import Minimmit.Analysis.Consistency.Lemma5_2
import Minimmit.Analysis.Consistency.Lemma5_3
import Minimmit.Analysis.Consistency.Lemma5_4
import Minimmit.Analysis.Liveness.Lemma5_5
import Minimmit.Analysis.Liveness.Lemma5_6
import Minimmit.Analysis.Liveness.Lemma5_7
import Minimmit.Analysis.Responsiveness.Lemma5_8
import Minimmit.Analysis.Responsiveness.Lemma5_9
import Minimmit.Analysis.Responsiveness.Lemma5_10
import Minimmit.Model.Constraint.Witness

/-!
# 主定理と依存公理

§5 の Lemma 5.1〜5.10 の定理と、制約の充足可能性の定理を 1 か所に並べ、それぞれが依存する
公理を `#guard_msgs` で固定する。依存公理が変わるか `sorry` が入ると、このファイルのビルドが
失敗する。`propext`・`Classical.choice`・`Quot.sound` は Lean の標準ライブラリと Mathlib が
使う公理。
-/

-- Lemma 5.1 One vote per view
/-- info: 'Minimmit.one_vote_per_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Minimmit.one_vote_per_view

-- Lemma 5.2 (X1)
/-- info: 'Minimmit.x1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Minimmit.x1

-- Lemma 5.3 (X2)
/-- info: 'Minimmit.x2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Minimmit.x2

-- Lemma 5.4 Consistency
/--
info: 'Minimmit.finalised_compatible' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Minimmit.finalised_compatible

/-- info: 'Minimmit.consistency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Minimmit.consistency

-- Lemma 5.5 Progression through views
/-- info: 'Minimmit.progression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Minimmit.progression

-- Lemma 5.6 Correct leaders finalise blocks
/--
info: 'Minimmit.correct_leader_finalises' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Minimmit.correct_leader_finalises

-- Lemma 5.7 Liveness
/-- info: 'Minimmit.liveness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Minimmit.liveness

-- Lemma 5.8
/--
info: 'Minimmit.correct_leader_finalises_fast' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in #print axioms Minimmit.correct_leader_finalises_fast

-- Lemma 5.9
/-- info: 'Minimmit.leave_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Minimmit.leave_view

-- Lemma 5.10 Optimistic responsiveness
/--
info: 'Minimmit.optimistic_responsiveness' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in #print axioms Minimmit.optimistic_responsiveness

-- 制約の充足可能性
/--
info: 'Minimmit.constraints_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Minimmit.constraints_satisfiable

/-- info: 'Minimmit.roundRobin_fair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Minimmit.roundRobin_fair
