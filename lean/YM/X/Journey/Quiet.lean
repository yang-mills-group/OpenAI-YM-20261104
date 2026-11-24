import YM.X.Journey.Quo
/-!
# Normalized stamp & periodic covariance interpretation at any center
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Crate.Fund
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics Reed Braid
open Clove Crystal Gravity Shelf Haze Ocean Interval Size Fielding Print PertExtension LatticePT Plate
open LiftMark Tensor Rays Hinge
open Stems hiding X
open scoped Topology ContDiff BigOperators Classical
variable {n:Side}{k:ℕ}{R:ℝ} {I:Type*} {G:Gauge}
open Porch
variable (q:ℕ+)(χ:Floor R)(S:Finset I)(P:I→Word G)(i:ℕ) (W:Word G)
local notation "regL"=> side q i
local notation "ε"=>epsilon q i
local notation "ℙ"=>flow G (side q i)
variable (x:I→Site (side q i)){F:Labels.Frames G}
def sphere_bill : ℂ:= ∑ z:Site regL,payer S q i P x (∑ j:PlaqAxes,hairAt z (vertex j))
def gate_bill (k:I):ℂ:=∑ z:Site regL, ((Floor.maskL q χ i) (lift z)) • (payer S q i P x (∑ j:PlaqAxes,hairAt (z+x k) (vertex j))) -- pulled location
variable (y:I→Fielding.Walk)(o:Site (side q i))
abbrev postal (y:I→Fielding.Walk) (o:Site n)(i:ℕ):= stock (fun j=> y j i) o
def far_bill : ℂ:= ∑ z:Site regL, Quiet q S y χ i z • (payer S q i P (postal y o i) (∑ j:PlaqAxes,hairAt (z+o) (vertex j)))
lemma far_wallet : sphere_bill q S P i (postal y o i)= far_bill q χ S P i y o + ∑ k∈ S,gate_bill q χ S P i (postal y o i) k := by
    let b(z:Site (side q i)):= payer S q i P (postal y o i) (∑ j:PlaqAxes,hairAt (z+o) (vertex j)); let t(k:I):= wrap regL (y k i); have hf (k:I): gate_bill q χ S P i (postal y o i) k=∑ z: Site regL, χ.s (spot (ε) (lift (z-t k))) • b z:= by
        conv_rhs=> rw [← Equiv.sum_comp (Equiv.addRight (t k))] 
        first | rfl | (unfold gate_bill;apply Finset.sum_congr rfl; intro j _; simp [b,t, Floor.masking,postal,stock,add_assoc])
    have he:sphere_bill q S P i (postal y o i) =∑ z:Site regL,b z:= by exact (Equiv.sum_comp (Equiv.addRight o) (fun z=> payer S q i P (postal y o i) (∑ j:PlaqAxes,hairAt z (vertex j)))).symm -- rw
    rw [he]; simp_rw [hf]; rw [Finset.sum_comm (s:=S)]; unfold far_bill; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _; unfold Quiet; rw [sub_smul,one_smul, Finset.sum_smul]; unfold b t; abel
variable [DecidableEq I] (p:I→ E4)(hp:∀ k∈S,plot q (y k) (p k)) {r:ℝ}(hR:Porch.Apart S p r)(hr:R<r)(z:∀ i,Site (side q i))(hq:1<q.val)
def due_bill (B:Bare.Shop F) :ℂ:= (∑ k∈ S,payer (S.erase k) q i P x (hairAt (x k) (mint ε (P k) 1 - rebate q χ i (P k) B))) - sphere_bill q S P i x
lemma due_lift (B:Bare.Shop F) : due_bill q χ S P i (postal y o i) B= (∑ k∈ S, neighbor q χ S P i (postal y o i) k B)- far_bill q χ S P i y o:= by rw [due_bill,far_wallet]; unfold neighbor; rw [Finset.sum_sub_distrib]; unfold gate_bill; abel
private lemma scale_verse (k:PlaqAxes)(z:Site (side q i)): spine ℙ (fun j=>dress (y j i) (milk ℙ (mint ε (P j) 0))) S (ε ^(-4:ℤ) • dress (lift z) (vertex k))= ε ^(-4:ℤ) • payer S q i P (postal y o i) (hairAt (z+o) (vertex k)):= by
    have he : payer S q i P (postal y o i) (hairAt (z+o) (vertex k))= spine ℙ (fun j=>dress (y j i) (milk ℙ (mint ε (P j) 0))) S (dress (lift z) (milk ℙ (vertex k))) := by nth_rw 1 [← wrap_lift z]; exact shoots ..
    rw [he,color_fire]; unfold spine; simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ), spiro.xscale, map_smul]
include hp hR hr hq
lemma far_walk : Released (fun i=> far_bill q χ S P i y (z i)) := by
    let q' (i:ℕ) (k:PlaqAxes) (t:Site (side q i)):= Quiet q S y χ i t • payer S q i P (postal y (z i) i) (hairAt (t+z i) (vertex k)); let s ( i k):=∑ t:Site (side q i), q' i k t; have he : 0<r:= χ.positive.trans hr; have h : Apart S p R := fun i hi j hj hn=> hr.trans (hR i hi j hj hn)
    have hy:Set.InjOn p S:= by intro i hi j hj heq; by_contra hn; have ht:= hR i hi j hj hn; rw [heq,sub_self,norm_zero] at ht; linarith
    have ht(i:ℕ):far_bill q χ S P i y (z i)=∑ k:PlaqAxes,s i k:= by unfold far_bill s q'; simp_rw [map_sum,Finset.smul_sum]; rw [Finset.sum_comm]
    simp_rw [ht]; apply Released.sumR; intro k _; let g(j):= urban (T:=Post) q Prod.fst (P j) (y j); let L:= lap S (travelers (T:=Post) Prod.fst q G) g (tower 4 q (vertex k));
    obtain ⟨a,ha⟩:= expand_suite hq S y p hp χ h (quiet_farm hq S y p hp χ h k g hy (fun k _=>urban_cost hq Prod.fst (y k) (P k)))
    refine ⟨a,ha.congr fun i=> ?_⟩; rw [Finset.smul_sum]; unfold s q'; apply Finset.sum_congr rfl; intro t _; change _ • (_ • spine _ (fun j=>urban q Prod.fst (P j) (y j) (i,(lift t))) _ (epsilon q i ^(-4:ℤ) • dress _ (vertex k)))=_; simp_rw [mint_urban]; change epsilon q i ^4 • (Quiet q S y χ i t • spine (flow G (side q i)) (fun j=> dress (y j i) _) S _) = _; rw [smul_comm (epsilon q i ^4:ℝ),scale_verse q S P i y (z i) k t,zpow_neg,zpow_ofNat,smul_smul (epsilon q i ^4:ℝ),mul_inv_cancel₀ (pow_pos (epsilon_pos q i) 4|>.ne'),one_smul]
lemma cost_bill (B:Bare.Shop F) : Released (fun i=> due_bill q χ S P i (postal y (z i) i) B):= by simp_rw [due_lift]; exact (Released.sumR _ (fun k hk=> street_near q χ S P y p hp hR hr hq k hk B z)).sub (far_walk q χ S P y p hp hR hr z hq)
end YM.PositionX.Crate.Fund
