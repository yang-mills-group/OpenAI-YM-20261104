import YM.FVA1.Station
import YM.FVA1.Garrison
set_option autoImplicit false
noncomputable section
namespace YM.FVA1
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Control Window Coat Footprint Raw Matter
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Stained Shield
open PhysicalNext PhysicalNext.Repeat Height Greenbelt
open Gas Ursell Trees RG.Supply Org Roost Opera
open Input Testing PriceCompiler
open AnalyticBridge VerifiedReset Collection Extra.Iteration Match Song Refrain Geo Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat.Daisy.Charity.RG12
open YM.RG01.Survive
open YM.ConnectedActivityE6.Blaze.Thermal1020
open YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
open UVExtension Spire Orchard Mast Oasis Progress.DirectedRecipe Mallow YM.RG12 OPE
open GridApprox.Nil Marker Merge MergeProof Accent
open YM.Overlay.GapsLocal GapsLocal Full Menu
variable {G:Gauge}
open UVNext.CouplingReset
variable (g:G.Simple) {X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Factor A}{L:Side}{m n N M k a b d: ℕ}{l v:ℝ}{Q: In A.B.a m n} (H: Spring R N m n l v Q)(x:Set.Icc l v)
set_option quotPrecheck false
local notation "j0" => A.B.a.clock.J m
local notation "i0" => A.B.a.clock.J (m+1)
local notation "s0" => A.B.a.clock.hatBeta m
local notation "k0" => Real.sqrt (A.B.a.clock.forcedAllowance m)
local notation "S'" => A.B.a.clock.op m n
local notation "W0" => Mallow.houseS H x
local notation "T0" => X.p.profile j0
local notation "Z" => horizonRadius G (D.L i0) s0
local notation "Cμ" => (R.shape.μ i0 j0)
variable {T ι V:Type}[Fintype ι][Fintype V][Nonempty ι][Nonempty V][DecidableEq V]{E':Marker.Census V}
variable (q:ι→Menu.Hat E' (Q x.val))(w:V→ℝ)(o: Positions V (A.B.a.S.side (m+1) n))
variable (read:ι→(V→T)→ℂ)(header:V→(V→T)→ℂ)
local notation "σ"=>shade w (shadowFactor G (D.L i0) s0 a)⁻¹
local notation "X₀"=> R.expense i0 j0
local notation "c0"=> A.B.a.budget m
local notation "c1"=> A.B.a.budget (m+1)
local notation "β"=> betaF G s0 (D.L i0)
local notation "βq"=> (Q x.val).beta
local notation "μs"=> straw Cμ (D.L i0) G s0
local notation "gP" p:max=> (Real.sqrt 2*Vacuum.nativeG βq)^(p+1)
local notation "α"=> fun i=> (Menu.heap q i).M
local notation "src"=> fun i=>sumFee (Menu.heap q i) σ
local notation "K!"=> Many.pupilK H x α src

set_option quotPrecheck false
-- a implicit captured in σ: must used parameters
local notation "D!" P:max => FVA1.cards (χ:=Chi.canonical) α src W0 K! (Full.target a b d) P
local notation "U₁"=> D! (fun _=>True)
local notation "U₂"=> D! (fun p:ℕ=>¬ Full.target a b d +1≤p)
local notation "U₃"=> D! (fun p:ℕ=>Full.target a b d+1 ≤p)
local notation "ch"=> (shadowFactor G (D.L i0) s0 a)
local notation "E0"=> H.result x
include g
-- full split on the masks of the constructed pressure. Calendar eventually supplies purchase premises.
local notation "Δ"=> FVA1.wind q read S' header σ E0 o U₁ U₂ U₃ -- FVA1 namespace ambiguity? inside YM.FVA1
local notation "target"=>Full.target a b d
variable [AddCommGroup T] [Module ℂ T]
variable (C:Controls V T)(hL:∀ i, SlotLinear (q i).s.val (read i))(hT:∀ i,SlotLinear ({i}:Finset V) (header i))(hq:∀ i x,C.Admits x→‖read i x‖≤1)(kX:ℝ)(hm':∀ i x,C.Admits x→w i*‖header i x‖≤kX)(hA:∀ i,∀ j∈(q i).s.val,o.stub j ⊆ (q i).M.crest)
include g hL hT hq hm' hA
omit [Nonempty V] in
set_option maxHeartbeats 680000 in
set_option maxRecDepth 2048 in
/-- Includes the rough any-arity operation at the reduced provisional radii σ;
input remains w. Uniformity at σ does not assert w-relative precision (recover w
*after fixed load*). Keep the stronger forced reserve. Absolute budgets before any
scalar- or field-coordinate reset.
-/
theorem uncap (hS:Mallow.RG12.Earned (markerBudget G) R.shape A.delay)(hPu:Pungent R.shape A.delay)(hR:Mallow.RG12.Earned (PhysicalNext.Repeat.FVA1.garrison G) R.shape A.delay)(h:m<N) (hs:Arrives R.shape A.delay)
   (he:100≤(c1).supportExponent)(he':100≤(c0).supportExponent)(hM:target+1 ≤ i0)
   (hw:Extra.Multi.Occupancy ((S').ratio.parent ∘ o.origin) i0)(hQ: Menu.Offer o.origin q w (Q x.val).p.B ((Q x.val).p.supportExponent-4) (Z^a))(hE:∀ i,0<w i):
    let X:=((Z)^(target+1))⁻¹
    let V:=(c0).supportExponent+1
    let k:= k0
    let u:=ch
    let t:=u^b
    let payb:=u⁻¹
    let D' := (Δ)
    0<k∧ k ≤1∧ 0< payb ∧ payb≤ 1 ∧ D'.Checks header (project (S') o) ∧
    D'.Invoice C σ V (payb*kX) 1 (k^target*X) X k ∧
    ((∀ i:E'.Mode,i.val.card ≤ b)→ D'.Invoice C w V (t*payb*kX) t (k^target*gP d) (gP d) k) ∧
    ∀ u, (S').push βq (MenuBridge.offered q read header u)= D'.whole.density u := by
  intro bill V k gain t μ F
  have h':= ballot g H x q w o (a:=a) (b:=b) (d:=d) hS hPu h hs he he' ((by omega): (Full.target a b d) ≤ i0) hw hQ hE
  dsimp only at h'; obtain ⟨hI,hC,_,hB⟩:=h'
  have ht:1≤Z:= by
    have he:=A.B.a.fits.delayed (m+1); rw [Push.PriceCompiler.beta_eq A.B.valid m] at he
    exact Real.one_le_rpow he.le (by norm_num [Thermal1020.ray])
  have hKr:k=Blush.glyph s0:= Blush.glyph_eq _ _
  have hK:0<k:= hKr ▸ Blush.glyphpos _
  have hG: k ≤1 := by rw [hKr]; unfold Blush.glyph; apply Real.sqrt_le_one.mpr; exact Real.exp_le_one_iff.mpr (by apply neg_nonpos.mpr; positivity)
  have hμ:0<μ:=by positivity
  have hw:∀ i,0<(σ) i:= shade_pos w hE hμ
  have hctx:=hR _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)
  have hW: Z^(target+1)*k⁻¹^(target+1)*μs ≤ 1:=hKr ▸ hctx _ hM
  have hX: μs ≤ (k^(target+1) * bill):=by
     rw [inv_pow, ← div_eq_mul_inv,div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hW
     unfold bill; rw [← div_eq_mul_inv,le_div_iff₀ (by positivity),mul_comm]; rwa [one_mul] at hW
  have hN: ∀ i x,C.Admits x → (σ) i * ‖header i x‖≤μ*kX:=by intro i x h; unfold Overlay.GapsLocal.shade; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hm' _ _ h) hμ.le
  obtain ⟨hQ,h⟩:=consumeRan q read S' header σ E0 _ _ _ o hI C hw hL hT hq hN hA hK (hX.trans_eq (by rw [pow_succ,mul_right_comm]))
  have hZ:0 ≤ t:=by positivity
  refine ⟨hK,hG,hμ,inv_le_one_of_one_le₀ hB, coiling q read S' header σ E0 _ _ _ o hI, hQ, fun hb=>?_, h⟩
  -- `F.tail.header` zero so 0*kX irrelevant, use mul_zero
  have hw(i:E'.Mode): Poly.toll w i ≤ t*Poly.toll σ i:= curveCost w i hE (hb i) hB
  have he : t*(k^target * bill) ≤ k^target * (gP d):=by rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left hC (by positivity)
  exact ⟨hQ.format,hQ.dossier.widen hE hZ hw (mul_assoc ..).ge (mul_one _).le he,
    hQ.marks.1.widen hE hZ hw (mul_assoc ..).ge (mul_one _).le he, hQ.marks.2.widen hE hZ hw (mul_zero _).le hC he⟩
end YM.FVA1
