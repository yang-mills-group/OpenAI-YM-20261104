import YM.X.Charting.Fee
import YM.X.Charting.Talent
import YM.X.Clear.Dona
/-!
Polynomial Wick gymnastics for one-row cutoff. Arbitrary varying locations. Real structure.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Hinge
open Function Filter Set Metric MeasureTheory Lattice Wilson PertExtension PertExtension.Series PertExtension.Series.Radial
open Source ProjectorNext.Calibration Gauss Next.Rank Normal MvPolynomial Finsupp
open Feyn Gauge LatticePT PertExtension.Orb Chart Stems PertExtension.Series.Tested Finset Interval Size Asymptotics
open Pert.Orb (formElem covar image takeDiv gZ positiveLinks wilson Potential form formL curL dLin bridgeEquiv)
open scoped Topology ContDiff BigOperators Classical RealInnerProductSpace
variable {G:Gauge} {n:Side} {q:ℕ+}(hq:1<q.val)
local notation "E"=> Potential G n
local notation "r"=> (atTop:Filter ℕ)
variable {α β V:Type*}
variable (x y:Beam q) (i j:Hair G)
abbrev shock (Q:Symmetric V) := blend Q 0

lemma ripe_mind (Q:ℕ→Symmetric V)(h:∀ i j:V,Ripe q (fun k=>(Q k).cov i j) 0) (p:poly V): Ripe q (fun k=> shock (Q k) p) 0:= by
   have hh : PolyFlow.Bounded Q r:= by intro i j; obtain ⟨c,hc,h⟩:= (h i j).exists_pos; exact ⟨c,h.bound.mono (fun k hk=>by simpa only [tickets_zero,norm_one,mul_one] using hk)⟩
   obtain ⟨B,hB⟩:= PolyFlow.bounded_mean hh p; exact Ripe.costed hB
lemma solstice {p f g H:ℕ→ℂ}(hf: Charged q p)(hg: Charged q H)(h:Vanished q (p-f))(he:Vanished q (g-H)) : Vanished q (p*g-f*H):= by
   rw [show p*g-f*H=p*(g-H)+(p-f)*H from by ring]; exact (Vanished.right hf he).add (h.left hg)
lemma supreme (a :ℂ){f:ℕ→ℂ}(h:Vanished q f): Vanished q (a • f):= Vanished.right (Charged.constant a) h
private lemma rise (s:Finset β)(x:β→V)(Q S:ℕ→Symmetric V)(hQ:∀ i j:V,Ripe q (fun k=>(Q k).cov i j) 0)(hS:∀ i j:V,Ripe q (fun k=>(S k).cov i j) 0)(h:∀ i j:V,Vanished q (fun k=>(Q k).cov i j-(S k).cov i j)):
     Vanished q (fun k=> shock (Q k) (glyphs x s)-shock (S k) (glyphs x s)):= by
   induction s using Finset.strongInduction with
   | _ s ih=>
     obtain rfl|⟨i,hi⟩:=s.eq_empty_or_nonempty; · simp only [glyphs,Finset.prod_empty,shock,Normal.fresh,sub_self]; exact Vanished.zero
     let p:=s.erase i; have he : s= Insert.insert i p:= (insert_erase hi).symm
     rw [he];simp_rw [shock,spring 0 _ x p (show i∉p from Finset.notMem_erase i s),Pi.zero_apply,zero_mul,zero_add,←Finset.sum_sub_distrib]
     apply Eq.mp ?_ (Vanished.finSum (f:=fun j=> (fun k=>(Q k).cov (x i) (x j) * shock (Q k) (glyphs x (p.erase j))-(S k).cov (x i) (x j)* shock (S k) (glyphs x (p.erase j)))) (s:=p) (fun j hj=> solstice (H:=fun k=>shock (S k) (glyphs x (p.erase j))) (Charged.of_pay (hQ (x i) (x j))) (Charged.of_pay (ripe_mind S hS (glyphs x (p.erase j)))) (h (x i) (x j)) (ih (p.erase j) (Finset.ssubset_of_subset_of_ssubset (erase_subset ..) (Finset.erase_ssubset hi))))) -- args
     congr 1; ext1 k; rw [Finset.sum_apply]
lemma blendsOf (Q S:ℕ→Symmetric V)(hQ:∀ i j:V,Ripe q (fun k=>(Q k).cov i j) 0)(hS:∀ i j:V,Ripe q (fun k=>(S k).cov i j) 0)(h:∀ i j:V,Vanished q (fun k=>(Q k).cov i j-(S k).cov i j))(p:poly V): Vanished q (fun k=>shock (Q k) p-shock (S k) p):= by
   induction p using MvPolynomial.induction_on' with
   | add p z h g => simp_rw [_root_.map_add,add_sub_add_comm]; exact h.add g
   | monomial i z=>
     obtain ⟨v,hv⟩:=Common.letter i; rw [show monomial i (z:ℂ)=z • glyphs v Finset.univ from ?_]; simp_rw [map_smul, ← smul_sub]; exact supreme z (rise Finset.univ v Q S hQ hS h)
     rw [←hv,← map_smul,smul_eq_mul,mul_one]

def remap (f:α→V)(Q:Symmetric V) : Symmetric α:= scope (fun i=> Finsupp.single (f i) 1) Q
lemma remaps (f:α→V)(Q:Symmetric V)(p:poly α): shock (remap f Q) p= shock Q (rename f p):= by unfold remap shock; rw [Normal.labelled, wets]; congr 2; ext1 i; simp [reads]
lemma renative (f:α→V)(Q:Symmetric V)(p:poly α): milk Q (rename f p)=rename f (milk (remap f Q) p):= by rw [Normal.labelled,prepared];rfl
lemma remap_cov (f:α→V)(Q:Symmetric V)(i j:α): (remap f Q).cov i j=Q.cov (f i) (f j) := match_name ..
end YM.PositionX.Hinge
