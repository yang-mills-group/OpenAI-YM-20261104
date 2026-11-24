import YM.OPE.Compatible.Tony.Curry
/-! # Education.Warm ambient path pulses. Hull actual h_at constructor includes ANY script.L eventually -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis Merchant.SiteL Flume.Page StepsL Wool
variable {i j d k m r l b:ℕ}{n:Side}
namespace Sleeve
variable {I:Type}{A:I→ Side}{a c:ℝ}{φ:Filter I}{Z:I→ℝ}{e:RootEdge}
variable {K:Sponsor G}{T:Seasons K}{v:I→ℝ}
variable (V:(j:I)→ Alps K T i (v j))
local notation "U!"=>GlyphQ G A
noncomputable def CircP (P:PathData G)(C:Clip)(u:Config G n):ℝ:= mainTerm C P u- mainTerm C P (1:Config G n)
lemma Kope (A:Alps K T i a)(x:Bid.Dir G n): Dune A x=CircP A.live A.clip (represent x):=by unfold CircP Dune; change mainTerm _ _ _-mainTerm _ _ _= _; rw[link_one]
noncomputable def mailP (c:Alps K T i a){n:Side}:Config G n→ℝ:= CircP c.live c.clip
noncomputable abbrev mailS (c:Alps K T i a){n:Side}: Config G n→ℝ:=Precision.loop c.live
variable (hc:G.Simple)(hp:RateLE φ Z v 0)(h: ∃ q,∀ i,(V i).clip=q) (ht:Tendsto Z φ atTop)
include hc ht
include h in lemma warming : Warm (HabitK A V) φ Z :=by
       obtain ⟨q,hq⟩:=h; constructor; intro k; let a:= cone (T.peak i /2) (k+1); have he:0<a:= peak _ _ (half_pos (T.positive _)); obtain ⟨C,hC,H⟩:= vats G q (T.peak i) (T.gradeL i) (T.positive i) (T.valL i) (k+1); let b:= ((k+1).factorial:ℝ); refine ⟨a,he,fun _=>‖b‖*C,RateLE.const _ ht,Eventually.of_forall fun j=>?_⟩; let X:=V j; have hp:X.live.Bounds q (T.peak i) (T.gradeL i) (v j):= hq j ▸ X.pays
       let v:=expose (oathX X.live q (k+1)); have hz:Felt v a (‖b‖*C):= Sack.scale_line (H X.live _ hp) _; refine ⟨v,(DuneAt X hc).sm,hz,fun y=>?_⟩; let z:=payroll X.live q hp (k+1) (A j) y; change library _ v _= iteratedFDeriv ℝ (k+1) (Dune X) 0 y; rw [Dune,iteratedFDeriv_sub_apply (show ContDiffAt ℝ _ _ _ from ((X.fullK 1).plot (A j)).of_le le_top) (show ContDiffAt ℝ _ _ _ from contDiffAt_const),iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k),Pi.zero_apply,sub_zero]; rw [show X.clip=q from hq j]; exact z
include hp
lemma warm_s: Warm (HabitL A V) φ Z:=by
       constructor; intro k; let a:=cone (T.peak i/2) (k+1); have he:0<a:= peak _ _ (half_pos (T.positive _)); obtain ⟨C,hC,H⟩:=va_roi G _ (T.positive i) (k+1); let b:= ((k+1).factorial:ℝ); refine ⟨a,he,fun j=>‖b‖*(C*(v j)),((RateLE.const _ ht).mul ((RateLE.const _ ht).mul hp)).mono (by norm_num),Eventually.of_forall fun i=>?_⟩; let x:=V i; exact ⟨_,(DuneAt _ hc).sg,Sack.scale_line (H x.clip x.live _ _ x.pays) b,fun y=> payrollL _ _ x.pays (k+1) _ y⟩
omit hc hp ht
-- construct Camera.B_Herm. Conditions mono. Seed.Pref.World
variable {V}
variable (K':Alps K T i a) (H:Board n b)
noncomputable def VoxM : Bid.Dir G n→ℝ:= mailP K' ∘ hermM H ∘ represent
noncomputable def VenM : Bid.Dir G n→ℝ:= mailS K' ∘ hermM H ∘ represent
lemma Advice : VoxM K' H=ᶠ[𝓝 0] Dune K' ∘ Λace G H:=by
       filter_upwards [Sphere H G] with i hi; unfold Function.comp at hi; simp only[VoxM, Function.comp_apply,Kope]; rw[hi]; rfl
lemma Zags: VenM K' H=ᶠ[𝓝 0] Rh K' ∘ Λace G H:=by filter_upwards [Sphere H G] with i hi; exact congr_arg (mailS K') hi.symm
lemma Consider : insured (tor n) (VoxM K' H)∧ insured (tor n) (VenM K' H):=by
        have he(x y:Bid.Dir G n)(s)(ht:(tor n).dress s (put x)=put y): VoxM K' H x= VoxM K' H y∧ VenM K' H x=VenM K' H y:=by
            obtain ⟨u,h⟩:= fieldKom H s (represent x); let v:= hermM H (represent x); have hx:= (Mar_ord ..).1 ht; rw [hx] at h; change CircP _ _ v=CircP _ _ (hermM H (represent y)) ∧ Precision.loop _ v=Precision.loop K'.live (hermM H (represent y)); rw [h]; exact ⟨sub_left_inj ..|>.mpr (((K'.fullK 1).stand ..).symm),((K'.fullL 1).stand ..).symm⟩
        exact ⟨⟨fun x y z h=> (he _ _ z h).1⟩,⟨fun x y z h=> (he _ _ z h).2⟩⟩
end Sleeve
end YM.OPE.Merchant
