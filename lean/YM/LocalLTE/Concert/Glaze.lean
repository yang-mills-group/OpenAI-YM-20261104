import YM.Extra.MULTISOURCE_TRAJECTORIES.Bands
import YM.Progress.DIRECTED_RECIPE.Pellets
import YM.LocalLTE.Port.Shift
/-! # One-sided glazed lemma

ExtraTest only read where eligible geometrically.
This is local attachment on the *same* true P. Do not put a trajectory on scratch!
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port
open Function Filter Set Lattice Wilson RG Overlay Marker Finset MeasureTheory
open Work.H03 Extra.Trajectories Progress.DirectedRecipe
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{n:Side} (P:Rep G n) (X:Activities G n)
-- modifies ALL addresses but only where tests ARE NOT read (by Road). eligibility itself? exact!
def ice (p:BudgetPoint) (y:ForcedAddress G n) : ForcedAddress G n:= {y with
    extraTest:= fun V=> y.support∩ flags p.threshold V=y.inventory→ y.extraTest V }
def glass (A:Rep G n) : Rep G n:= {A with activities := {A.activities with forced:=ice A.p ∘ A.activities.forced } }
lemma ice_eq (p:BudgetPoint) (y:ForcedAddress G n) (U:Config G n): (ice p y).eligible p.threshold U ↔ y.eligible p.threshold U:=by simp only [ice,ForcedAddress.eligible]; tauto
lemma filmA (s:BudgetPoint) (i:ℕ)(p:Activities.ForcedFamily X s)(U:Config G n): 
    UsesFinal s.threshold (ice s (X.forced i)).support (ice s (X.forced i)).extraTest ∧ (∀ k,(ice s (X.forced i)).extraTest (gauge k U) ↔ (ice s (X.forced i)).extraTest U)∧ MeasurableSet {V| (ice s (X.forced i)).extraTest V}:=by
    let F:= X.forced i; let Y:= ice s F; let t(V:Config G n):Prop := F.support∩ flags s.threshold V=F.inventory
    refine ⟨fun U V hG hF=> ?_,fun k=>?_,?_⟩
    · change (F.support∩ flags s.threshold U=F.inventory→ (X.forced i).extraTest U)= (F.support∩ flags s.threshold V=F.inventory→ (X.forced i).extraTest V); change F.support∩ flags s.threshold _=F.support∩ flags s.threshold _ at hF; rw [hF,(p.reads_test i U V hG hF)]
    · change (F.support∩ flags s.threshold (gauge k U)=F.inventory→ (X.forced i).extraTest _ ) ↔ (F.support∩ flags s.threshold U=F.inventory→ F.extraTest U); rw [gauge_flags,p.symtest]
    let F':ForcedAddress G n:= {F with extraTest:= fun _=>True}; have he {V}:t V=F'.eligible s.threshold V:=by simp only [t,ForcedAddress.eligible,F',and_true]
    rw [show {V|(ice s (X.forced i)).extraTest V}= {V| F'.eligible s.threshold V}ᶜ∪ {V| (X.forced i).extraTest V} by ext V; change (t V→ _) ↔ _; rw [he]; simp only [Set.mem_union,Set.mem_compl_iff,Set.mem_setOf_eq]; tauto]; exact ((eligible_measurable _ F' MeasurableSet.univ).compl).union (p.meas_test i)
lemma frosted {d k:ℝ}(h:P.activities.Valid P.p d k): (glass P).activities.Valid P.p d k:=by
    let A:=P.activities; let B:= (glass P).activities; let R:=P.p; have ht:=h.forced
    refine ⟨⟨h.regular.smooth,h.regular.at_flat,h.regular.vanish⟩,⟨ht.sym,fun i a U=>(filmA _ R i ht U).2.1 a,ht.meas,fun i=>(filmA _ R i ht 1).2.2,ht.reads,fun i=>(filmA _ R i ht 1).1,fun i U h=> (ice_eq _ _ U).2 (ht.permit i U h)⟩,fun s a=> ?_,h.boundE,h.boundK⟩
    obtain ⟨y⟩:= h.moves s a; refine ⟨y.ep,y.kp,y.reg_site,y.reg_support,y.forced_support,y.forced_inventory,?_,y.valuesE,y.valuesK⟩
    intro i U
    have hf : Injective (affine s a):=fun _ _ h=>s.act_injective (add_right_cancel h)
    simp only [glass,ice,Function.comp_apply,y.forced_support,y.forced_inventory,y.forced_tests,← flags_send s a P.p.threshold U,← Finset.image_inter _ _ hf,(Finset.image_injective hf).eq_iff]
lemma gallery (h: HasSlots P.p P.activities):Extra.Trajectories.Aperture (glass P):=by
    intro a; let k:Foot n:= ⟨a.wall,a.bill,a.needs,a.inside⟩; let i:= sleepK G n (k,0); let y:= P.activities.forced i; let p:= P.p
    have hi: readFoot y=k:=by unfold y; rw [h.forced]; exact tile_exact ..
    refine ⟨i,congr_arg Foot.support hi,congr_arg Foot.inventory hi,fun U (hU:y.support∩ flags p.threshold U=y.inventory)=> ?_⟩
    change y.extraTest U; unfold y; rw [h.forced]; exact (tile_test p k 0 U).2 ((congr_arg (·∩ flags p.threshold U) (congr_arg Foot.support hi).symm).trans (hU.trans (congr_arg Foot.inventory hi)))
variable {V:Type}[Fintype V][DecidableEq V] (R:Census V)
def overB (Y:Bands R (glass P)) : Bands R P:=⟨Y.origins,Y.units,Y.support,Y.rays,Y.H,Y.marks,Y.entries⟩
variable (Y:Bands R (glass P))
omit [Fintype V] in
lemma portedB(h:Y.Active): (overB P R Y).Active:= ⟨h.proper,h.pins,h.regular,h.occurs,h.retained,h.inspects,fun i j U h' => (ice_eq _ _ U).1 (h.keeps i j U h'), h.meas,h.invi⟩
omit [Fintype V] in
lemma portedP {r:V→ℝ}{a b d e:ℝ}(h:Y.Radial r a b d e): (overB P R Y).Radial r a b d e:= ⟨h.pure,h.localU,h.factor,h.bulk,h.hits⟩
lemma portedE (U:Config G n): (overB P R Y).density U= Y.density U:=rfl
section layers
variable {α:Type}(X : Layers P R α) [Fintype α][Nonempty V]
def glace : Layers (glass P) R α:=⟨X.origins,X.units,X.region,X.tag,X.H⟩
def posta:= overB P R (glace P R X|>.bands)
local notation "U'"=> glace P R X
omit [Fintype V][Fintype α][Nonempty V] in
lemma glacis(h:X.Ready): (glace P R X).Ready:= ⟨⟨h.proper,h.home⟩,h.regular⟩
omit [Fintype V] in
lemma frostD(h:HasSlots P.p P.activities)(hr:X.Ready){a b:ℝ}(hp:P.activities.Valid P.p a b): (posta P R X).Active:= portedB P R _ ((U').active (gallery P h) (glacis P R X hr) (frosted P hp).forced)
lemma nocturne(h:HasSlots P.p P.activities)(hr:X.Ready){a b:ℝ}(hp:P.activities.Valid P.p a b) (U:Config G n): (posta P R X).density U = (P.eval U : ℂ) • Poly.pass (X.logPart U):= (portedE P R _ U).trans ((U').exact_density (gallery P h) (glacis P R X hr|>.toAnchored) (frosted P hp) U)
end layers
end YM.LocalLTE.Port
