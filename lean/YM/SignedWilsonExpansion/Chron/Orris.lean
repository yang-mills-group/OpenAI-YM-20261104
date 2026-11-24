import YM.SignedWilsonExpansion.Chron.FerryP
import YM.SignedWilsonExpansion.Chron.Membrane
import YM.WilsonCoeffUV.Marked.Capture.AtSensor
/-! Pulse equivalence from original socket slate including stops. No ℂ-linearity assumed on stencils. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.Integration.Liner
open Function Matrix Lattice RG Laurent Bloch Gauge
open WilsonCoeffUV WilsonCoeffUV.Blue FreeResolvent Tree WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Power
open WilsonCoeffUV.Bank WilsonCoeffUV.Soil Exterior Source WilsonCoeffUV.Embroider
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Mer.Xa
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark Lattice Laurent Labels Precision PowerSeries
open WilsonCoeffUV.Bank.Mosaic
open PhysicalNext.Repeat.Legato Wilson Stationary Finset
open OriginalMarkedSourceComet IndependentSourcePathFamily
open ActualRunCurvaturePackets WilsonCoeffUV.Mer.Xa.Corps -- fix
open ActualRunGradedKernels (rank section_valuation)
open WilsonOriginalStarLaurentWallet (Socket lag shape)
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{J:Type}{k m f r ℓ h N c v e n:ℕ}{A: ChartRatio G}
local notation "ι'"=> Fin (n+1)
variable (R:Run G)(D d: Fin (n+1) →ℕ)(pt: Fin (n+1)→ Chamber)
variable (S:Finset (Fin (n+1)))(o:Fin (n+1) → Cover)
-- Horizon θ includes kinetic reparam. power-variable remains same across coordinates
abbrev trailG (f:(i:Fin (n+1))→ Cursor R (d i)):= independent (fun (j:Fin (n+1)) (_:Unit)=> petS R (d j) (D j) (pt j) (f j))
abbrev flameG (j:Fin (n+1))(a:Cursor R (d j)):= mount D j (petS R (d j) (D j) (pt j) a) (o j)

lemma warmthG (f:(i:Fin (n+1))→ Cursor R (d i)): Eu d (trailG R D d pt f o) := IndependentSourcePathFamily.legal _ _ fun j _=> paysS ..
lemma simmer (f:(i:Fin (n+1))→ Cursor R (d i)): tuftV (touch (lamp D) univ) (levelsO (trailG R D d pt f o) univ)=MassP G ℝ n (fun i=>flameG R D d pt o i (f i)):=by
    let t:= trailG R D d pt f o; let X i:=flameG R D d pt o i (f i); have he:=warmthG R D d pt o f; have hv : t ∅=0:= IndependentSourcePathFamily.empty ..; have ht s : s.card≠1 → t s=0:=fun h=> Finset.sum_eq_zero fun j _=> dif_neg (by intro hz; exact h (by rw [←hz, card_singleton]))
    have hx i: X i=tuftV (touch (lamp D) {i}) (t {i}):=by unfold t trailG; rw [IndependentSourcePathFamily.singleton]; unfold IndependentSourcePathFamily.single; rw [Fintype.sum_unique]; rfl
    have hu(i):Auth (d i) (X i):= certifiedL _ _ _ (paysS ..) _; apply flash_recover (Auth.tuft (placedO _ he _) _) (manCo X d hu); intro p
    change feeble (levelsO t) (lamp D) p univ=Blue.flash ((MassP G ℝ n X).1 p); rw [Wheel.Flooring.firstExp (levels_exp t he hv (lamp D) p) (fun i h=>by rw [feeble,ht i h,read_emp]),Wheel.Flooring.poly_agate n X d hu]; exact Finset.prod_congr rfl fun i _=>by rw [hx]; rfl

abbrev phi (g θ:ℝ)(x:(i: Fin (n+1))→ R.family.label (d i))(K:Levels G)(A:ChartRatio G)(N:ℕ)(r v:ℕ): InkQ :=
    ∑ f:(i:Fin (n+1))→ Cursor R (d i), (∏ i:Fin (n+1), stick R (d i) g θ (x i) (f i)) • insertQ (FadeRaw K A N (mass d univ) r v (tuftV (touch (lamp D) univ) (levelsO (trailG R D d pt f o) univ))) -- actual iteration **full tattoos**
lemma bridge (g θ:ℝ)(x:(i: Fin (n+1))→ R.family.label (d i))(K:Levels G)(s:G.Simple)(hb:LocalRatio A)(q:r≤ v)(b:v ≤ N)(t:∀ i,d i≤k):
    phi R D d pt o g θ x K A N r v= MergeTrip.dockD d (fun i=>R.family.localSection ( d i )) (fun i=> life R (d i) g θ (x i)) K A N k r v o:=by
   let F (i):=(R.family.labels.level (d i)); let T (i):=R.family.localSection (d i); let Z (i):=stick R (d i) g θ (x i); let Y (i): F i |>.Coeff := life R (d i) g θ (x i); let V:= flameG R D d pt o; let L (i)(a:(F i).Index): Era G ℝ:= shifted (Looms.literal (T i) a) (o i)
   have hv i p: Auth (d i) (V i p):= certifiedL _ _ _ (paysS ..) _; let σ':= mass d univ; have hs:σ'≤(n+1)*k:=by unfold σ' mass; exact (Finset.sum_le_sum (g:=fun _=>k) fun i _=>t i).trans (by simp)
   unfold phi; simp_rw [simmer]; have hx (f:(i:Fin (n+1))→ Cursor R (d i)): let P:=MassP G ℝ n fun i=> V i (f i); FadeRaw K A N (mass d univ) r v P=FadeRaw K A N ((n+1)*k) r v P:=by intro P; exact congr_arg Mer.Xa.dew (growingK s hb q b hs P (manCo _ d fun i=> hv i _))
   change (∑ f:(i:Fin (n+1))→ Cursor R (d i), _ • insertQ (FadeRaw K A N _ r v (MassP G ℝ n fun i=> V i (f i))))= _; simp_rw [hx]; refine (Corps.Leaves (dance L Y V Z ?_ (fun i j=> (Looms.strength _ (section_valuation R (d i)) (R.makes.sections (d i)) (t i)).shifted _) (fun i j=> (hv i j).tall (t i))) (fun i=> MassP_auth _ (fun j=> (Looms.strength _ (section_valuation R (d j)) ( R.makes.sections (d j)) (t j) ).shifted _ )) (fun i=> MassP_auth _ (fun j=> (hv j _).tall (t j))) s hb q b).symm
   intro i
   exact life_shift D R (d i) i (pt i) (o i) g θ (x i) -- binder order
end YM.Integration.Liner
