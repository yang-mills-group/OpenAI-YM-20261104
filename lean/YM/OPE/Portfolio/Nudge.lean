import YM.OPE.Portfolio.Cordons
import YM.OPE.Sweep.Induct
/-! # Products met exactly at native meshes.

Instantiate at each regulator independently. No relation between witness Cup choices
in distinct layouts. Use same `Contracts` geometry when requiring joint prices;
avoid requirement that any subterm of a genuine primary be reflection invariant. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Cadet
open Function Filter Finset Lattice RG Wilson Pressure MeasureTheory
open Push Marker Accent Menu Extra.Multi Extra.Trajectories Ribbon Source Local
open Extra.Histories PhysicalNext.Repeat Lotus GridApprox.Nil OPE.Backup Motion
open Muster MergeProof.Float
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {V : Type}[Fintype V][DecidableEq V]{G:Gauge}{H:History G}{N p m i b:ℕ}
set_option quotPrecheck false
variable (L:Playout H p m N V){I J:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]
namespace Playout
variable {u:I→Site (H.S.side i p)}{u':J→Site (H.S.side i p)}{s:Ward (Names V I)}{s':Ward (Names V J)}{W:I→ℝ}{W':J→ℝ}
    {f:I→ Cup (H.rep N p i)} (X:I→ Config G (H.S.side N p)→ℂ)
local notation "T"=> H.rep N p
local notation "F"=> (fun i=> stepUp (L.tint (Prod.fst i)) (L.positions N (Prod.fst i)) (X (Prod.snd i)))
-- additional radius `x` price; horizon W.V.CPP
variable {x:ℝ}
def statute := birth (Names V I) (H.rep N p N) (F)
def intention (i)(hi:i≤N):= gust H N p N (L.statute X) i hi
lemma intention_step (he:i<N) : L.intention X i he.le = (H.levels.clock.op i p).push ((T (i+1)).beta) (L.intention X (i+1) he):= gust_step _ _ _ _ _ he
-- family persistence
lemma intend_cont (h:H.Selected)(ht:∀ i,Continuous (X i)): Continuous (L.statute X) :=by
    have hx(a:V×I):Continuous (F a):=by unfold stepUp Motion.scalar;dsimp only;split;exact ((ht _).comp (continuous_pull ..)).star; exact (ht _).comp (continuous_pull ..) -- F hidden arg
    have hp : Continuous (T N).eval:=by rw [(h.starts ..).2]; exact bare_cont _ -- namespace
    apply (Complex.continuous_ofReal.comp hp).smul; change Continuous (fun U=> Poly.pass (Mach _ (fun a=> F a U)))
    apply Poly.pass_cont.comp ?_
    apply continuous_finsetSum; intro i _; change Continuous (fun U=>(Poly.send ((Names V I).fire i) (F i U)).part); apply continuous_pi; intro j; simp_rw [Poly.part_send]; split_ifs; exact hx i; exact continuous_const
lemma paidFor (h:H.Selected)(ht:∀ i,Continuous (X i))(he:i≤N): Integrable (L.intention X i he) (prior G _):= gust_live _ _ _ _ _ ((L.intend_cont X h ht).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) he
local notation "f'"=> Pigment.sweep V
-- linear per-branch
open Pigment
variable (A:I→J)(C:I→ℂ){M:Type*}[AddCommMonoid M][SMul ℂ M]
def linear (t:I→M)(j:J):= ∑ i∈ residents A j,C i • t i
local notation "σ"=> L.skater C
lemma tintL {g:I→ Res G (H.S.side i p)}(v:V)(j:J) : floatUp (L.tint v) (L.positions i v) (linear A C g j)=∑ b∈ residents A j,σ (v,b) • floatUp (L.tint v) (L.positions i v) (g b):=by
    funext x U; unfold linear floatUp stepUp skater; simp_rw [Finset.sum_apply,summer,Pi.smul_apply,smul_eq_mul,scalar_mul]
lemma tintP (i:ℕ){g:I→ Config G (H.S.side i p)→ℂ}(v:V)(j:J): stepUp (L.tint v) (L.positions i v) (linear A C g j)=∑ b∈ residents A j,σ (v,b) • stepUp (L.tint v) (L.positions i v) (g b):=by
    funext U; unfold linear stepUp skater; simp_rw [Finset.sum_apply,summer,Pi.smul_apply,smul_eq_mul,scalar_mul]
lemma flags_solo (h:H.Selected)(ht:∀ i,Continuous (X i))(hi:i≤ N)(U:Config G (H.S.side i p)) : homL (Pigment.sweep V A) (L.skater C) (L.intention X i hi U)=L.intention (linear A C X) i hi U:=by
    induction hi using Nat.decreasingInduction with
    | self=> unfold intention statute; rw [gust_base,gust_base]; rw [born_with]; congr 2; funext i; exact (L.tintP A C N i.1 i.2).symm
    | of_succ i hi IH=> rw [L.intention_step X hi, L.intention_step (linear A C X) hi,Pigment.pushes _ _ _ _ U (H.levels.transition_mass ..) (L.paidFor X h ht hi)]; rw [show (Pigment.homL (Pigment.sweep V A) (σ) ∘ L.intention X (i+1) hi) = _ from funext (fun i=>IH i)] -- `..` syntax
lemma Market.changeChannels (he:i≤N)(h:H.Selected)(ht:∀ i,Continuous (X i)) (hp:L.Market s u f (L.intention X i he) W x)
    (hz:∀ i,C i≠0 → u' (A i)=u i)(hh:∀ i,W' (A i)*‖C i‖≤ W i)(hw:∀ i,0<W' i)
    (hL:∀ i:(Names V I).Mode,s'.ready (batch (f' A) i)→ Set.InjOn (f' A) i.val → (∀ j:V×I,j∈i.val → C j.snd≠0) → s.ready i): L.Market s' u' (linear A C f) (L.intention (linear A C X) i he) W' x:=by
    let z:= f' A; have hf: L.cupsReg i (linear A C f)= palette A (σ) (L.cupsReg i f):=by
       funext j; unfold cupsReg linear palette; rw [Cup.summing]; exact L.tintP (g:=fun i=>(f i).home) A C i j.1 j.2 -- smul Cup not simp
    have hF:L.cupsRes i (linear A C f)= palette A (σ) (L.cupsRes i f):=by
       funext j; unfold cupsRes linear palette; rw [Cup.summingKey]; exact L.tintL (g:=fun i=>(f i).leaves) A C j.1 j.2
    refine ⟨hw,?_⟩; rw [hf,hF, show L.intention (linear A C X) i he = homL z (σ) ∘ L.intention X i he from (funext ((flags_solo L X A C h ht he))).symm ]; apply Pigment.coats _ _ hp.tall ?_ ?_ (fun i=> hw i.snd|>.le) (fun i=> hp.width i.snd|>.le) ?_ ?_
    · intro j hj; unfold spectrum Pigment.sweep; change affine _ _ (u' (A j.2)) = affine _ _ (u _); rw [hz j.2 (by unfold skater at hj; exact fun hp=> hj (by rw [hp,scalar_z]))]; rfl
    · intro j; unfold skater; rw [norm_scalar]; exact hh j.snd
    · intro i _ j; rw [L.pepped]; rfl
    intro i he hr hv; apply hL i he hr; intro j hj ht; have h:=hv j hj; unfold skater at h; apply h; rw [ht,scalar_z]
-- grouping primitive
namespace Rake
variable (D:Fibers I J)
def grouped_X (j:J)(U) := ∏ i∈D.contents j,X i U
local notation "K"=>partialGroup V D
lemma cont (ht:∀ i,Continuous (X i))(j:J) :Continuous (Rake.grouped_X X D j):= continuous_finsetProd _ fun i _=> ht i
lemma intention_eq (h:H.Selected)(ht:∀ i,Continuous (X i))(hi:i≤N)(U:Config G (H.S.side i p)): Fibers.reap (partialGroup V D) (L.intention X i hi U)=L.intention (grouped_X X D) i hi U:=by
    induction hi using Nat.decreasingInduction with
    | self => unfold intention statute; rw [gust_base,gust_base]; ext i; change (birth _ _ _ U).part ((K).plena i)=_; unfold birth Mach; simp_rw [Poly.part_smul,pass_fire]; rw [Fibers.prod_plena]; refine congr_arg _ (prod_congr rfl fun j hj=>?_ ); rcases j with ⟨v,j⟩; rw [contentP, prod_image] ; change _ = stepUp _ _ (grouped_X X D j) U; unfold stepUp grouped_X scalar; split; exact (star_prod ..).symm; rfl
              exact fun _ _ _ _ hp=> Prod.mk.inj hp|>.2
    | of_succ i hi IH=>
       let a := L.intention X (i+1) hi; let b:= L.intention (grouped_X X D) (i+1) hi; let S:= H.levels.clock.op i p
       have hh := ((Fibers.reap (partialGroup V D)).restrictScalars ℝ).integral_comp_comm (StepData.push_slice (H.levels.transition_mass i p (T (i+1)).beta) U a (L.paidFor X h ht hi)); simp_rw [map_smul] at hh; rw [L.intention_step X hi,L.intention_step (grouped_X X D) hi]; have hz:b=(fun U=>Fibers.reap (K) (a U)):= (funext IH).symm; change _= S.push _ b _; rw [hz]; exact hh.symm
end Rake
end Playout
end YM.MergeProof.Ribbons.ManyCopies.Cadet
