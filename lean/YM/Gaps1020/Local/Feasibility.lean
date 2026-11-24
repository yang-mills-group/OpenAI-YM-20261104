import YM.Gaps1020.Local.Widen
set_option autoImplicit false
noncomputable section
namespace YM.GapsLocal.Full
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
open YM.ConnectedActivityE6.Blaze.Thermal1020
open YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
open UVExtension Spire Orchard Mast Oasis Progress.DirectedRecipe Mallow YM.RG12 OPE
open GridApprox.Nil Marker Merge MergeProof Accent
variable {G:Gauge}
section one
variable {ι V:Type}[Fintype ι][Fintype V][Nonempty V][DecidableEq V]{E':Marker.Census V}
variable {c f L:Side}{W s μ C:ℝ}{S:StepData c f}{T: Tube G S}{P:Teller G}{Q: ConnectedActivityE6.Target G P}{o: Target.Order G W}
    {R:RG.Rep G f}(H:Cash W s μ L Q o C T R)
    (E0:RG.Rep G c)(M':ι→ Lotus.Leaf R)(rA:ι→ℝ)(g:ι→Poly E')(K:ℝ→ Finset ι→ Ovens.Code G c)(v': V→Site c)(i:V→ℂ)
local notation "χ" => Chi.canonical
local notation "Δ" u:max s:max M:max => scenery M' (H:=H) rA g s u v' E0 K χ M
variable {z t τ κ ρ v v1 v2 v3 v4:ℝ} {N M j a n:ℕ}{p:ℝ}{o':V→Site f}
    {w w':V→ℝ}
open YM.Overlay.GapsLocal
lemma widenClaim (h:Claim H E0 M' rA g K v' i M w v v1 v2 κ)(he:∀ s:E'.Mode,Poly.toll w' s ≤ z*Poly.toll w s)(hz:0≤z)(hs: z*v1≤v3)(hr:z*v2≤v4)(hw:∀ i,0<w' i)(ht:∀ j, w' j*‖i j‖ ≤ t): Claim H E0 M' rA g K v' i M w' t v3 v4 κ:=by
   exact { h with complete:=⟨h.complete.1, shiftBill _ hw z hz h.complete.2 ht he hr hs⟩, funded:=⟨h.funded.1,shiftBill _ hw z hz h.funded.2 ht he hr hs⟩, remainder:=⟨h.remainder.1, shiftBill (Δ 0 (fun p=>M+1 ≤ p) M) hw z hz h.remainder.2 (fun i=>by change _*‖(0:ℂ)‖≤_; simp only [norm_zero,mul_zero]; exact le_rfl) he hs hs⟩ }
-- quantitative debt; deliberately don't align unit budgets or marks with hull on support
open Menu in
-- billing. Works with E and K in same Hat
omit [Nonempty V] in
lemma feasible (u:ι→Hat E' R)(ht:Menu.Offer o' u w R.p.B (R.p.supportExponent-4) p)(hh:Extra.Multi.Occupancy (S.ratio.parent ∘ o') N)
      (hQ:Palette.shipPrice L Q s N p)(he:4 ≤ Q.relative)(hy:100 ≤ R.p.supportExponent)(hd: Daisy.foam Q L)(hv:R.p.B≤2*radiusB s)(hV:∀ i,0<w i)(hp:0≤p) :
    let f:=fun i=>(u i).M; let r:=fun i=>Menu.sumFee (u i) w
    Palette.Thermal.BuysMix f H r∧∀ i, Scoped {x| (S.ratio.parent ∘ o') x∈ (f i).crest.image S.ratio.parent} (Menu.sing (u i) w):=by
   intro f r
   let A i:=(u i).s.val
   have ha i x (hx:x∈A i): o' x∈ (u i).M.crest:= ht.sites i (mem_image_of_mem _ hx)
   refine ⟨Palette.Thermal.extendsDeck f H r (fun i=> timed _ hV) o' A hh ?_ he hy hd hv hp ?_ hQ, fun i=> scope_send _ _ _ (fun x hx=>mem_image_of_mem _ (ha _ _ hx))⟩
   · intro i _; obtain ⟨j,hj⟩:= (u i).shiny; exact ⟨j,hj,ha _ _ hj⟩
   intro i; refine budget_mono (ht.budget (o' i)) (fun _=>?_) (fun i'=> ?_)
   · split; exact mul_nonneg (Real.exp_pos _).le (Crew _ hV); exact le_rfl
   split; next hj=> rw [if_pos (ha _ _ hj),mul_comm]; exact le_rfl
   next=> exact (ht.budget ..).1 _

abbrev shadowFactor (G:Gauge)(L:Side)(s:ℝ)(d:ℕ):ℝ:= horizonRadius G L s^(d+5)
local notation "β" => betaF G s L
local notation "Z" => horizonRadius G L s
local notation "X*" d => shadowFactor G L s d
omit [Fintype V] [Fintype ι] [Nonempty V] [DecidableEq V] in
lemma shadowPays (hy:1≤β) (d:ℕ) : ((X* d))⁻¹ * Z^d ≤ Mallow.probe β:=by
   have hx:1 ≤ Z:=Real.one_le_rpow hy (by norm_num [Thermal1020.ray])
   unfold shadowFactor; rw [pow_add, inv_mul_le_iff₀ (by positivity)]; apply le_mul_of_one_le_right (pow_nonneg (by linarith) _) (show _ ≤ (Z^5)*Mallow.probe β from ?_)|>.trans_eq (mul_assoc ..).symm
   unfold Mallow.probe horizonRadius; rw [← Real.rpow_mul_natCast (by linarith) Thermal1020.ray,← Real.rpow_add (by linarith)]
   exact Real.one_le_rpow hy (by norm_num [Thermal1020.ray])

open Menu in
omit [Nonempty V] [Fintype V] in -- [Fintype ι] needed Heap
lemma deckPrice (ht: Tariff Q L N μ s)(hh:1≤ β)(q:ι→Hat E' R)(hw:∀ i,0<w i) (h: Menu.Offer o' q w R.p.B z (Z^a))(hv:0≤z):
    Menu.Offer o' (heap q) (shade w ((X* a))⁻¹) R.p.B z (Mallow.station β):=by
   let i := (X* a); have hx:1 ≤ i:= one_le_pow₀ (Real.one_le_rpow hh (by norm_num [Thermal1020.ray]))
   let s0:= shade w i⁻¹; have ha:0< i⁻¹:=by positivity
   let y:= Mallow.probe β; have he: Offer o' q s0 R.p.B z y:= offerPrice q hw h ha (by rw [inv_le_one₀ (by linarith)]; exact hx) (shadowPays hh a)
   let p:= radiusTab (radiusB β) N y; have hy:0<y:= ht.probeT
   have hh:y ≤ p:=by
      unfold p radiusTab
      have hv:0≤ Extra.Multi.siteFactor (radiusB β):=by unfold Extra.Multi.siteFactor; positivity
      exact le_add_of_nonneg_of_le (by positivity) (by linarith)
   exact (counts q s0 o' _ (shade_pos _ hw ha) (he.fatten hh) hv).fatten ht.buy
-- just prove measure fit via Carrier budget. No lossy canopy E-cost.
end one
end YM.GapsLocal.Full
