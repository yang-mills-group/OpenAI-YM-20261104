import YM.OPE.Compatible.Eyrie.Shrub
import YM.MergeProof.Canyon
import YM.OPE.Compatible.Eyrie.Aurora
/-! # Suns under linear growth. All period errors in `.fuse`, arbitrarily fast along p only after horizon/family. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Guard Next.Foundations Local Next.Rank Edition Spindle Extra.Multi Motion
open PhysicalNext.Repeat.Legato.Bandage Cells Extraction Extraction.Lease Exponential Bid Next.Extract RelayDifference Opening
open Labels OPE.Eyrie
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}(H:C.Makes)(B:Stock.Tabs C.path.levels)
variable {f:Extraction.Order}{N p k d:ℕ}(V:SectionData (C.labels.level d))(hV:V.Sound C.params)
    {ζ:ℕ→ℕ→ℝ}{E:ℕ→ℝ}{P:ℕ→ℕ→(C.label d≃ₗ[ℂ] C.label d)}{U:ℕ→ℕ→(C.labels.level d).Index→ C.label d}
    (h:Hearth V ζ E P U) (h': Sun V E U)
set_option quotPrecheck false
local notation "F"=> C.labels.level d
local notation "T"=> C.localSection d
local notation "Φ"=> C.path
local notation "s'"=> (Size.axis (C.labels.level d))
local notation "ρ"=> Motion.Tally (C.labels.level d)
variable (x : Rowe C d)
local notation "Y"=> (fun j:Cutoffs=> (C.factory d j.1 j.2).terminal ((P j.1 j.2) (x j)))
include h h' H hV
def screens (Z0: Family G)(Z: Trial Z0)(d:ℕ)(f:Extraction.Order):Prop:=∀ k,Z0.ref d ≤ k→ ∀ D:ℕ→ℝ,(∀ i,0<D i)→∀ᶠ i:ℕ×ℕ in f.fuse,∀ hk:k≤ i.1,∀ U,‖OPE.Eyrie.puff Z0.path i.1 i.2 d (Z i.1 i.2 0) hk U‖≤Real.exp (rhoE (Z0.path.rep i.1 i.2 k))*D i.2
set_option maxRecDepth 4096 in
lemma saddle (he:Slow C f x) : screens C (upper C Y-hallmarks V x) d f:=by
      intro k hk D hD
      choose b hb hB using fun p=> nik_enroll H hk p
      let Q (a:ρ) := hallmarks T (fun j=> Motion.patch F a.1 (U j.1 j.2 a.2)) - hallmarks V (fun j=> Motion.patch F a.1 (s' a.2)); let S(a:ρ)(j:Cutoffs):=Motion.chips F (x j) a
      have hr(j:ρ):Slow C f (S j):=by
         let a:= Motion.share* orbitCost F; have hp:= (Slow.const (C:=C) a).mul (coords_slow x he); refine hp.reduce (Eventually.of_forall fun i=> ?_)
         rw [show S j i=chips F (x i) j from rfl,norm_chips]; exact (mul_le_mul_of_nonneg_left ((BasisCost.coord_le _ _).trans (patch_cost ..)) share_pos.le).trans (le_trans (le_of_eq (mul_assoc _ _ _).symm) (Real.le_norm_self _))
      let W(i:Cutoffs):= ∑ j:ρ,‖S j i‖*E i.1; have hw:Slow C f W:= Slow.sum _ _ (fun i _=> (hr i).norm.mul (h.coined f)); filter_upwards [(cutoff_grows f).eventually h.stamped,(cutoff_grows f).eventually h'.stamps,taxi b W hw k hD] with i hi hI hv hu Z
      let e j:= OPE.Eyrie.puff C.path i.1 i.2 d (Q j i.1 i.2 0) hu Z; let w:= Real.exp (rhoE (C.path.rep i.1 i.2 k)); let N:=i.1; let p:=i.2;
      have ht {Y₁ : SectionData (C.labels.level d)}(y:C.label d):Continuous (initial Y₁ C.path N p y 0):= by unfold initial; exact (Y₁.continuous_places _ _).const_smul _
      have hh(j:ρ):Continuous (Q j i.1 i.2 0):= by change Continuous (_ - (initial V C.path N p _ 0)); exact (ht _).sub (ht _)
      have hz(j:ρ): ‖e j‖ ≤ w*b p*(E N/gainChart C.path N k):=by
             let X:= U N p j.2; let a:=j.1; let v:=s' j.2
             let f:= initial T C.path N p X 0; let g:=initial V C.path N p v 0
             have he : Q j i.1 i.2 0 = dance a (f-g):= by
                rw [show dance a (f-g)= dance a f-dance a g from funext fun U=>by unfold dance scalar;split <;>simp]
                change hallmarks T _ i.1 i.2 0- hallmarks V _ i.1 i.2 0 =_ -- notation hmk
                unfold f g; rw [signed_intro C T (H.sections d), signed_intro C V hV]; rfl
             unfold e; rw [he,twig C.path hu (f-g) ((ht X).sub (ht _)) d a]; unfold dance; rw [norm_scalar, show f-g = ((-1:ℂ) • (g-f)) from by rw [neg_one_smul,_root_.neg_sub], Opal C.path hu (g-f) ((ht _).sub (ht _))]; simp only [Pi.smul_apply,smul_eq_mul,norm_mul,norm_neg,norm_one,one_mul]; exact (hI p j.2) k hk hu _ (hb p) (hB p) _
      have hy: gathered Q S i.1 i.2 = (upper C Y-hallmarks V x) i.1 i.2 := by
         funext a; rcases i with ⟨N,p⟩
         let i:Cutoffs:=(N,p); let V0 := P i.1 i.2; let J:ρ→ℂ:= fun s=> S s i; let g (u):= initial V C.path i.1 i.2 u a
         let F' u:=initial T C.path i.1 i.2 u a
         have hx: IsLinearMap ℂ g:= notationL C.path d _ V i.1 i.2 a; have hF:IsLinearMap ℂ F':= notationL C.path d _ T i.1 i.2 a; let f:= IsLinearMap.mk' _ hx; let x':= IsLinearMap.mk' _ hF
         let x'' : Lattice.Site _ → Config G (C.side i.1 i.2)→ℂ:=C.O i.1 i.2 (d:=d) (Y i)
         have hy : x'' a=F' (V0 (x i)):=by unfold x'' Family.O TransferData.cylinder; rw [LinearEquiv.symm_apply_apply] -- name
         change (∑ j:ρ,J j • (x' (Motion.patch F j.1 (U i.1 i.2 j.2)) - f (Motion.patch F j.1 (s' j.2))))= x'' a-f (x i)
         simp_rw [smul_sub,Finset.sum_sub_distrib,←map_smul,←map_sum]
         rw [hy,show V0 (x i)= decor F (U i.1 i.2) (x i) from (hi i.2).1 _,decor_eqQ]
         change x' (repaint F (U i.1 i.2) (x i)) - f (repaint F (s') (x i))= x' _- f (x i)
         rw [show repaint F (s') (x i)=x i from repaint_same F LinearMap.id (fun x i=>rfl) _]
      let V(j):= Q j i.1 i.2 0
      rw [← hy,show gathered Q S i.1 i.2 0= ∑ j:ρ,S j i • V j from rfl,balloons d _ _ (fun j=> (hh j).const_smul _) hu, Finset.sum_apply]
      refine (norm_sum_le ..).trans ?_; have hh(j:ρ): ‖OPE.Eyrie.puff C.path i.1 i.2 d (S j i • V j) hu Z‖≤ (w*b p/gainChart C.path i.1 k)*(‖S j i‖*E i.1):= by
          rw [Opal C.path hu (V j) (hh j),Pi.smul_apply,smul_eq_mul,norm_mul]; exact (mul_le_mul_of_nonneg_left (hz j) (norm_nonneg _)).trans_eq (by unfold N; ring)
      apply le_trans (Finset.sum_le_sum (fun i _=> hh i)); rw [← Finset.mul_sum]; exact le_trans (le_of_eq (show (w*b p/gainChart C.path i.1 k)* W i=_ from Eq.trans (by ring : (w*b p/gainChart C.path i.1 k)* W i=w*(b p*W i/gainChart C.path i.1 k)) rfl)) (mul_le_mul_of_nonneg_left hv (Real.exp_pos _|>.le))
end YM.MergeProof
