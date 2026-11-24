import YM.OPE.Compatible.Copper.Adjust
/-!
# both lens readings and room views of root balance at weighted grants. choose sign trigger aperture externally; asserted for every layout; existence paired. quota of marked parent survives exactly. Uniform in characters. Polynomial in march and aperture clocks, along one profile.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset Extraction Word Spec
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb Allot Lights Wave Relay Cells CutOrder Arcade Pixel
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {X I J' : Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X){U F:Finset X}
   {G:Gauge}{C:Family G}{Λ:Extraction.Order}{S:Table C.book}(T:Spec.Final C Λ S)(A:Allot C) (P:Prescription T.sector.derivatives)
variable (p:X→ C.book.Token) (u:X)(hu:u∈rest U)
set_option quotPrecheck false
local notation "L"=> T.sector.derivatives
local notation "V"=> brim D U
local notation "W"=> brim D (Arboreal.trim U u)
local notation "J"=> glen D U u
local notation "p₀"=> picked V p
variable (hI:Inward C Λ S)(h:Services C Λ S)
    (d:ℕ) {b c K k q:ℕ}
variable {φ:Filter I}{s:I→X→ℝ}{r:I→ℝ} [Fintype J'] (w:J'→ C.book.Token)
    (a:Mode T.sector.derivatives){η M t:ℝ}(hL:Glowing D U φ r s η)
local notation "R"=>fun i=> volume D U (fun x:V=>(p₀ x).1) (s i)*(s i (par D u)/s i u)^d/(s i ⊥)^a.fst
local notation "L'"=>fun i=> area D (fun x:V=>(p₀ x).1) (s i) (cove D U u)/s i u^d
local notation "O!"=>fun i=> aperture D C b c η (r i) (s i)
local notation "at!"=>fun i=> schedule C b η (s i)
-- needs output bound via mode top 
include A h hL hI hu T
variable (hP:P.Coherent)(hO:Outward C Λ S T.sector.derivatives)
lemma highestCoverage (hp:0≤ M)(hb:1 ≤ b) (hc:d ≤ b)(ht:0<t)(hP:P.Coherent)(hO:Outward C Λ S T.sector.derivatives) :
    ∃ f f':I→ℝ,Round φ r (fun i=> f i * L' i)∧ Round φ r (fun i=> f' i * R i)∧ ∀ᶠ i in φ,
       whenHigh U (at! i)= at! i u → O! i u ≤ at! i u-1 → ∀ z:X→E4, Ridge (s i) η M D U z → Screened D U C z (O! i)→∃ y:C.label d,∃ t':C.label a.fst,
       (∀ i' ∈ bands L d, ‖P.ope i' (picked J z) (picked J p) (z u)-P.test i' d (S.project d y)‖ ≤ f i) ∧ ‖P.test a a.fst (S.project _ t')‖ ≤ f' i ∧
       (∀ i'∈ bands L a.fst, ‖(P.ope i' (picked V z) p₀ 0-P.ope i' (picked W z) (picked W (update p u (⟨d,y⟩:C.book.Token))) 0)-P.test i' a.fst (S.project a.fst t')‖≤ f' i) ∧
       ∀ s':J'→E4, ClearOf 0 s' t →∀ q:Viewers T, ‖(observe (spectator T q) (beside (picked V z) s') (beside p₀ w)-observe (spectator T q) (beside (picked W z) s') (beside (picked W (update p u (⟨d,y⟩: C.book.Token))) w))- observe (spectator T q) (beside (sole (0:E4)) s') (beside (sole (⟨a.fst,t'⟩: C.book.Token)) w)‖≤ f' i :=by
   let U':=hL.crowned; let e:=a.fst; let s'':=viewed_root (T:=T) h.schedule w ht
   have ho: u∈U:=(rest_mem ..).mp hu|>.2; have ho': u≠⊥:= (rest_mem ..).mp hu|>.1; let T':= Arboreal.trim U u; have hF:= remains _ U' ho'; let κ i:= schedule C b η (s i) ⊥-1
   obtain ⟨k,⟨b',B,hb',hB,hV⟩,⟨c',B',hc',hB',hV'⟩,A₀,hA,hW'⟩:=((tunes T P d h.schedule).and ((storyFunds D T P p u U' hu h.schedule (bands L e)).and s'')).exists
   obtain ⟨n,hK'⟩:= A.buy.tabs.mayOpen C.path.levels 1 k
   have hU(i:ℕ):Stock.Tabs.opens C.path.levels 1 k (max n (C.ref i)):= A.buy.tabs.open_later C.path.levels 1 hK' (le_max_left ..) zero_le_one
   obtain ⟨x,x',z,z',hx,hx',hz,hz',hY⟩:=deposit D A h.simpleGate T.room.cutoff hL p₀ ho hI hp ho' hb hc (hU d) (hU e) (le_max_right ..) (le_max_right ..) (l':=c)
   -- inspect paper syntax
   obtain ⟨M',hM'⟩:= hO.paper a.fst a.fst le_rfl (P.test a a.fst) (fun j hj hf v=> by rw [P.affinity T.room.kernel.laws.toSymmetric T.phase.transport.injection,Prescription.highVan _ _ hP _ hj]; exacts [T.room.kernel.laws.toSymmetric,T.phase.transport.injection])
   obtain ⟨_,hR',hβ,_⟩:= prev_info D h.simpleGate A hL b
   let u₀ i:= x' i*(B+1); let u₁ i:= z' i*(B'+A₀+1)+ (β C (κ i)^M')*z i
   refine ⟨u₀,u₁,(hx'.mul (Round.const (a:=B+1) (by positivity) hL.ray)).adjust (Eventually.of_forall fun i=>by unfold u₀; ring), ((hz'.mul (Round.const (a:=B'+A₀+1) (by positivity) hL.ray)).sum ((hβ.power M' hL.ray).mul hz) hL.ray).adjust (Eventually.of_forall fun i=>by unfold u₁ e κ; ring),?_⟩
   filter_upwards [hY,allure D (M:=M) hb' hL,allure D (M:=M) hc' hL,allure D (M:=M) ht hL,hR'.eventually hM'] with i hi hΨ hv₀ hv' hI hq hs z₀ hZ hZ'
   let γ:= Address.mk hZ (shutter_final _ _ U' z₀ hZ'.angel) hZ'.stops -- inspect type inference
   obtain ⟨K',y,hK,hZ'',hε⟩:= Address.pack D (j:=k) γ U'; let Y:=C.S.gridPoint K' ∘ y
   have hΛ:Ridge (s i) η M D U Y:=by
       have hx':∀ l∈ allUp D U,Y l=z₀ l:=fun l hl=> (hZ'' _ hl).2; constructor
       · rw [hx' _ (mem_union_left _ U'.base)]; exact hZ.belly
       · intro x y hx hy hl; rw [hx' x (mem_union_left _ hx),hx' y hy]; exact hZ.near x y hx hy hl
       intro x y hx hy hl hh; rw [hx' x hx,hx' y hy]; exact hZ.span _ _ hx hy hl hh
   obtain ⟨p',hK',q,t',hW⟩:= hi hq hs K' y hΛ hε (fun i hi=> ⟨(hZ'' _ hi).1,(hZ'.stops i hi).imp fun b hb=>(hZ'' _ hi).2.trans hb.symm⟩); obtain ⟨q',hσ,hY'⟩:= coverPaint p (F:=V) p' hK'; rw [show (fun y:brim D U=>(⟨(p₀ y).1,p' y⟩:C.book.Token)) = picked _ q' from hσ.symm] at hW
   have hq(i)(hi:i ∈ allUp D U) : Y i=z₀ i:= (hZ'' _ hi).2
   have hv(a:Mode L)(hA:a∈bands L d): ‖P.ope a (picked J z₀) (picked J p) (z₀ u)-P.test a d (S.project d q)‖≤ u₀ i:=by
       let x':= picked J (fun i=>y i-y u); have he:= swivelMine D u hW; let e₀:=centeredAway D hq ho
       rw [inCentered D T p hq ho]
       apply (hV hK (p:=picked J p) (fun a=>hY' _ (Finset.mem_filter.mp a.2|>.1)) he (shore_screen D hZ'.angel U' hq ho) (fun a=>?_) a hA).trans
       swap
       · change ‖(C.S.gridPoint K' ∘ picked _ _) _‖ < _; rw [e₀]; exact (hΨ z₀ hZ a.val (mem_union_right _ (mem_filter.mp a.2|>.1))).2 u (mem_union_left _ ho)
       exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (token_fees D u hW).1
   let a₀:= u₁ i; obtain ⟨hu_,hy⟩:= token_fees D u hW
   have h : ‖P.test a a.fst (S.project _ t')‖ ≤ β C (κ i)^M'*z i:=by
       obtain ⟨_,_,f,hf,he,F,hU,g',hg',hΛ⟩:= hW; simpa using (hI f hf he g' _ (z i) hg' (hΛ.mono (fun _ hh=>hh.tell)))
   have hx : 0 ≤ z' i*(B'+A₀+1):=by positivity -- z' i ? syntax
   have hE : z' i*(B'+A₀+1)≤ u₁ i:= le_add_of_nonneg_right ((norm_nonneg _).trans h)
   have hc : V⊆allUp D U:= Finset.subset_union_right; have hc':brim D T' ⊆ allUp D U:= brim_under D U T' (filter_subset ..)
   have hp:= take_plan D hc Y hq; have hp':= take_plan D hc' Y hq
   have hh : Screen (picked (brim D U) z₀):= shutter_final D U U' z₀ hZ'.angel; have hh':= onAny D hZ'.angel T' (filter_subset ..) hF
   refine ⟨q,t',hv,h.trans (le_add_of_nonneg_left hx),fun a ha=>?_,fun s' hJ r'=>?_⟩
   · rw [← hp,← hp']; apply (hV' K' hK y q' (hp.symm ▸ hh) (hp'.symm ▸ hh') (fun i hi =>hv₀ Y hΛ i hi|>.1) hY' hW a ha).trans; exact (mul_le_mul_of_nonneg_left (by linarith : B' ≤ B'+A₀+1) hy).trans hE
   have hx(A:Finset X)(hc:A⊆allUp D U)(hx:Screen (picked A z₀)): Injective (beside (picked A Y) s'):=by
       rw [take_plan D hc Y hq]
       refine beside_distinct.mpr ⟨hx.coin,(beside_distinct.mp (hJ.inject_both ht)).2.1,fun k m hh=>?_⟩; have hf:= hv' z₀ hZ k.val (hc k.2)|>.1; change ‖picked A z₀ k‖ < t at hf;rw [hh] at hf; have he:= hJ.openSpace m; rw [zero_sub,norm_neg] at he; linarith
   rw [← hp,← hp']; apply (hW' K' hK D U u U' (by assumption) p q' hY' y (hp.symm ▸ hh) (hp'.symm ▸ hh') hW _ hJ (hx _ hc hh) (hx _ hc' hh') r').trans; exact (mul_le_mul_of_nonneg_left (by linarith : A₀ ≤ B'+A₀+1) hy).trans hE
end YM.OPE.Arboreal.Trace
