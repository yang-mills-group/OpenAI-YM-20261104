import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Assets
/-! # One simultaneous salary (de-filtering on actual fields). Includes polynomial exponents
independent of `B` (indeed stronger range). -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Original
open Function Filter Set MeasureTheory Asymptotics Lattice Wilson RG Source Extraction Table Spec
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Climb Maxwell XSpace XSpace.Normalize XSpace.Structure1 OPE OPE.Orbits PhysMS
open FVA2.Scale Comparing O.Score O.Enh Dframe ScaleCost Matrix Flash259HorizonFork
open scoped Topology BigOperators Classical Matrix
local notation "late" => 𝓝[>] (0:ℝ)
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Z : ℝ→PhysMS.tower S) (Q:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {N : WilsonPrescription G} {ν : ℝ}
    {O : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {sim : G.Simple}
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim O σ dial)
    {t : ℝ→ℝ} (hZ : Leading F Z) (hq : ∀ d, FieldQuote G (GroupS.gaugeN N.scheme N.criterion O ν) t (via Z) d 1)
    (hQ:LogTrace F Q.port)

variable {I J K : Type}[Fintype I][Fintype K]{l : Filter J} {s r : J→ℝ}
    (hs : Tendsto s l late)
    {x:J→ I→E4} {y:J→ K→E4}{o:J→ E4} {M δ:ℝ}(mn:0≤M)(dp:0<δ)
    (hx : ∀ᶠ i in l,Flash259HorizonFork.Ready (r i) (s i) M δ (x i) (y i))
    {d:I→ℕ}{e:K→ℕ} {u:J→(i:I)→Sec G (d i)}{v:J→(j:K)→Sec G (e j)}
    (hu:∀ (i:I) (b:Toon G (d i)),Allowance l r (fun _=>1) (fun j=>coord b (u j i)))
    (hv:∀ (i:K) (b:Toon G (e i)),Allowance l r (fun _=>1) (fun j=>coord b (v j i)))
    (p:J→Viewers F) {h:ℕ}

-- use currency Γ' via `Allowance` ⇒ common ∑ delta widths. Exponent independent of b on
-- **two length** estimate. Can directly choose here.
include hs hx sim
private lemma fraction {E : Type*} [NormedAddCommGroup E] {f:J→ℝ} {p:J→E} (H : Allowance l r f p) (hf : ∀ᶠ i in l,0 ≤ f i) :
    ∃ Z : ℕ, ∀ z:ℕ, Z ≤ z → ∃ C' : ℝ, 0 < C' ∧ ∀ᶠ i in l, ‖p i‖ ≤ C'*(g0 G (r i))⁻¹^z*f i := by
  have hr:=smaller_radius hs hx; obtain ⟨K,hK,k,H⟩:=Allowance.budget hr H hf
  have be (q): OPE.Log.badge q=1+cash q:=by rw [OPE.Log.badge,OPE.run,cash,Real.log_inv]
  let a := G.slopeConstant⁻¹; have ha : 0 < a := inv_pos.mpr (Gauge.slopeConstant_pos sim)
  refine ⟨2*k,fun z h=> ⟨K*(1+a)^k,by positivity,?_⟩⟩
  have e := (pace sim).comp hr
  filter_upwards [now e, near e, hr.eventually (adjustment sim), H, hf, log_pays hr] with i hi hL eq V W z'
  apply V.trans; apply mul_le_mul_of_nonneg_right _ W
  rw [be] at *; rw [eq] at *
  -- division & powers estimate
  let u:=(g0 G (r i))⁻¹; have hv : 1 ≤ u := (one_le_inv₀ (show 0 < g0 G (r i) from hi)).mpr hL
  calc K*(1+G.slopeConstant⁻¹*u^2)^k ≤ K*((1+a)*u^2)^k := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by change 0 ≤ 1+a*u^2; positivity) (by change 1+a*u^2 ≤ _; nlinarith [show 1 ≤ u^2 from one_le_pow₀ hv]) _) hK.le
       _ = K*(1+a)^k*u^(2*k) := by rw [mul_pow,pow_mul]; ring
       _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hv h) (by positivity)
abbrev trueY (F:Final C f S) (Z:ℝ→PhysMS.tower S) {d:I→ℕ}{e:K→ℕ} (r s : ℝ) (o : E4) (p:Viewers F)
    (x:I→ E4)(y:K→E4)(u:(i:I)→Sec G (d i))(v:(i:K)→Sec G (e i)) :=
  Orbits.whole (spectator F p) (atPosition o r x) (enter Z r u) (atPosition o s y) (enter Z s v)
abbrev trueD (F:Final C f S) (Z:ℝ→PhysMS.tower S) {e:K→ℕ} (r s:ℝ)(o:E4)(p:Viewers F)
    (y:K→E4)(v:(i:K)→Sec G (e i))(h:ℕ) := testCentre F Z h p o (atPosition o s y) (enter Z s v) r
abbrev trueC (r:ℝ)(o:E4)(x:I→E4)(u:(i:I)→Sec G (d i))(h:ℕ) :=
   (frame Z r h).symm (Q.packet h (atPosition o r x) (enter Z r u) o)

include H mn dp hZ hq hQ hu hv
local notation "w" => fun i:J=> s i + (r i/s i)^(h+1)
local notation "YY" p:max => (fun i:J=>trueY F Z (r i) (s i) (o i) (p i) (x i) (y i) (u i) (v i))
local notation "DD" p:max => (fun i:J=>trueD F Z (r i) (s i) (o i) (p i) (y i) (v i) h)
local notation "cc" => (fun i:J=>trueC F Z Q (r i) (o i) (x i) (u i) h)
local notation "normC" => fun c=> tallyZ (numbers (G:=G) (h:=h) c)
-- one witness for all bounds; filter app.
lemma salaries (q:J→Viewers F) : ∃ C:ℝ, 0<C ∧ ∃ z:ℕ, ∀ᶠ i in l,
    let b:=C*(g0 G (r i))⁻¹^z
    ‖(YY p) i-(DD p) i (cc i)‖ ≤ b*w i ∧
      ‖(YY p) i‖+normC (cc i) + opCost ((DD p) i) ≤ b ∧
      ‖(YY p) i-(YY q) i‖+opCost ((DD p) i-(DD q) i) ≤ b*s i := by
  have hr:=smaller_radius hs hx
  have hb : Allowance l r w (fun i=> (YY p) i-(DD p) i (cc i)) := by
    refine (paid_discrepancy F Z Q H hZ hq hQ hs (o:=o) mn dp hx hu hv p).congr ?_; refine Eventually.of_forall fun i=> ?_; dsimp only; unfold trueY trueD trueC discrepancy testCentre; rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  let B i:=‖(YY p) i‖+normC (cc i)+opCost ((DD p) i); let S i:= ‖(YY p) i-(YY q) i‖+opCost ((DD p) i-(DD q) i)
  have E:Allowance l r (fun _=>1) B := by
    refine Allowance.add hr (Allowance.add hr (worth F Z Q H hZ hq hQ hs (o:=o) mn dp hx hu hv p|>.norm) ?_) ?_
    · exact Allowance.sum hr _ _ fun i (_:i∈(Finset.univ:Finset (Toon G h)))=> Allowance.norm (field_quote F Z Q H hZ hq hQ hs (o:=o) mn dp hx hu hv i)
    exact Allowance.sum hr _ _ fun i (_:i∈(Finset.univ:Finset (Toon G h)))=> Allowance.norm (center_budget F Z Q H hZ hq hQ hs (o:=o) mn dp hx hv p i)
  have A: Allowance l r s S := Allowance.add hr (split_phase F Z Q H hZ hq hQ hs (o:=o) mn dp hx hu hv p q|>.norm)
      (Allowance.sum hr _ _ fun i (_:i∈(Finset.univ:Finset (Toon G h)))=> Allowance.norm (center_phase F Z Q H hZ hq hQ hs (o:=o) mn dp hx hv p q i))
  have ha : ∀ᶠ i in l,0 ≤ w i := hx.mono fun i h=>by dsimp only; have v:= h.length; have e:=v.trans_le h.adj; positivity
  have hS: ∀ᶠ i in l,0 ≤ s i := hx.mono fun i h=>h.length.le.trans h.adj
  obtain ⟨l,h⟩:= fraction (sim:=sim) hs hx hb ha; obtain ⟨k,z⟩:= fraction (sim:=sim) hs hx E (Eventually.of_forall fun _=>zero_le_one); obtain ⟨j,u⟩:=fraction (sim:=sim) hs hx A hS
  let C:= k+l+j
  obtain ⟨F,i,f⟩:=h C (by omega); obtain ⟨K,k0,e⟩:=z C (by omega); obtain ⟨M,m,r'⟩:=u C (by omega)
  refine ⟨F+K+M,by positivity,C,?_⟩; filter_upwards [f,e,r',ha,hS,now ((pace sim).comp hr)] with i' f e v l z a
  dsimp only; change ‖B i'‖ ≤ _ at e; change ‖S i'‖ ≤ _ at v
  let r:=(g0 G (r i'))⁻¹^C; have a : 0 ≤ r := pow_nonneg (inv_nonneg.mpr a.le) _
  have b:B i' ≤ (F+K+M)*r := (le_abs_self _).trans (e.trans (by rw [mul_one]; apply mul_le_mul_of_nonneg_right _ a; linarith))
  have h : S i' ≤ (F+K+M)*r*s i' := (le_abs_self _).trans (v.trans (by apply mul_le_mul_of_nonneg_right _ z; apply mul_le_mul_of_nonneg_right _ a; linarith))
  exact ⟨f.trans (by apply mul_le_mul_of_nonneg_right _ l; apply mul_le_mul_of_nonneg_right _ a; linarith),b,h⟩

end YM.FVA2.GradedFar259.Original
