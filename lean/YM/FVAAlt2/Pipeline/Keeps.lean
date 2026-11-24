import YM.FVAAlt2.Pipeline.Memory
/-! # Actual-Run dynamic programming. Every admitted Reader is buying the same coefficients through its price (same V.Gamma). -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Pipeline
open Function Set Filter Finset MeasureTheory Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Geometry Prim Diagram Diagram.Formal PertExtension Series Series.Radial Series.Tested Chart Binding Ledger Gauge Booth
open Lattice RG Precision Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Adjacent Comparison.RG02.FVAAlt2 Integral Wilson Exterior Arm Marker Multi
open PowerSeries
open scoped Topology BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {m :ℕ} {G:Gauge} {R X:Type} [DecidableEq R] {Q:KernelChoices} {M:X→ℕ} {N:Page M→Side}
open Oracle Period.Field
variable (C:Circuit M N) (Y:Oracle.Program Q)(Φ:∀ P:Patch,P.Branches Q G) (Γ: History G)(K: Bulk.Chain Γ)(P: Period.Field.SeriesT C Q Γ)
variable (S: Marker.Census R)(u:R) (A: X→ Boot.Scout (G:=G) m)
variable (L:Page M→ Binding.Scale)
variable (p:ℕ) -- period
namespace See
variable {C Γ}
local notation:max "x_" k:max=> P.vol k
set_option quotPrecheck false
local notation:max "f_" k:max => (Γ.S.side (P.vol k) p)
local notation:max "U_" k:max => P.stepData C Γ p k
local notation:max "F_" k:max => Halo.bios ( P.stepData C Γ p k )
local notation:max "P_" k:max => P.records C Γ p k
local notation:max "J_" k:max => directive (P.stepData C Γ p k)
local notation:max "K_" k:max => ( P.readyKin C Γ K p k )
local notation:max "w_" k:max=> Page.opening M k
local notation:max "B_" k:max=> ( Boot.ink S u Γ (P.vol (w_ k)) p (A k) )

open FreeResolvent (flatten)
-- degree equality & exceptive. propagate both ways!
local notation:max "Z_" x:max => C.bore G Φ L x
local notation "Z"=> work Φ K P L p
local notation "W"=> observe Φ K P A L p
variable (r:ℕ)(T:Times (L:=L) r)[Fintype R]
local notation:max "t_" k:max => T.cloth k
local notation:max "Z₀" k:max=> Recv P p k ( Z (Flap.prev k ))
local notation:max "W₀" k:max=> Recv P p k ( W (Flap.prev k ))
local notation "R!"=> Prepared Φ K P S u A L p r T
variable (hL:∀ x:X,L (Page.opening M x)= Clocks.flat)
-- cast across relation. height cutoff.Stable
variable (i:Flap M)(y:Colors S G (Γ.S.side (P.vol i.prev) p))(y': Colors S G (Γ.S.side (P.vol i.next) p))
local notation "p₁"=> P_ i.next
local notation "y₀"=> before P i y
local notation "B"=> C.tables Y i.prev
local notation:max "V_" k:max => ( Uniforms.cloth (P_ k).clip (P_ k).path (Z k) )
local notation:max "b_" k:max => ( Uniforms.cuff (W k) m )
local notation "Γ'"=>lifeT K P S (p:=p) L r T i y
local notation "Γm"=> boostT K P S u (p:=p) L r T i y

lemma isReal {c:Side}(q: RG.Clip) (k: PathData G)(v:Orders (Pin c G))(L:UnitCost)(Z':Colors S G c)(H': Simmer q k L Z' v r)(b:fieldDir G c 1) (e:ℕ) (he:e≤r): visible S q k L Z' e b= Uniforms.cloth q k v e b:=by
    unfold visible Uniforms.cloth; split <;> rename_i h
    · subst e; rw [ Binding.flavor_dark _ (Binding.vacuum_lo _ H'.wakes) _,Complex.ofReal_zero,add_zero ]
    rw [← H'.cost _ (Nat.pos_of_ne_zero h) he];simp
lemma blocked0 (e:ℕ): V_ i.next e 0=0:=by
    unfold Uniforms.cloth; let U:=Z i.next; rw [flavor_lo, show flatten _= (0:FreeResolvent.Vec G (f_ i.next) 1) from rfl, ← Prim.speaking, Prim.starts, itinerary];
    have hp: U e 0=0:=by unfold U; rw [itinerary]; unfold riseV Arm.OutputV Binding.pulp; rw [if_pos rfl]
    simp_rw [show riseV Φ K P L p i (Z i.prev) e 0=0 from (by rw [← itinerary]; exact hp),Pi.zero_apply,Complex.ofReal_zero,add_zero]; split <;> first| rfl | simp [Assembly.jet]
    exact ContinuousMultilinearMap.map_zero (iteratedFDeriv ..) 
variable (h : Prepared Φ K P S u A L p r T i.prev y)
include h Y
lemma twins (e:ℕ)(he:e≤r) : Γ' e - (fun _=> Γ' e 0)= V_ i.next e:=by
    obtain ⟨hv,hZ,hv'⟩:= progressed Φ K P S u A L p r T i y h
    let D':= scriptV (U_ i) (F_ i) (K_ i) (Z_ i) (Z₀ i); let G'(j:ℕ):=(↑(coeff j (Binding.out D')):ℂ); let H'(j:ℕ):= Comparison.RG02.Moving.Path.motion (fun t=> (Aperture.earn (F_ i) (G:=G) (t_ i.prev) t:ℂ)) j
    have hz : ∀ x:fieldDir G (f_ i.next) 1,(V_ i.next) e x = (Γ' e x+ H' e)- G' e := by
       intro x; rw [itinerary]; exact Uniforms.contact (U_ i) (F_ i) (L i.prev) (K_ i) (t_ i.prev) (Geometry.Field.Square.proper _ _) (Z_ i) (Z₀ i) y₀ r (T.holds i.prev) (poster_h Φ P L p i) hv (Γ.levels.budget (P.vol i.prev)) B (P.upstream Y C Γ K p i) (Thermal.maps K (P.start C Γ i.volW) (P.vol i.next) p (P.fresh C Γ i) _ _) x e he
    have hx:= hz 0; rw [blocked0] at hx; funext x; rw [hz]; change Γ' e x-Γ' e 0=_; rw [show Γ' e (0:fieldDir G (f_ i.next) 1)=G' e-H' e from eq_sub_of_add_eq ( sub_eq_zero.mp hx.symm ) ]; abel
lemma stamps (e:ℕ)(he:e≤r) : Γm e=b_ i.next e:=by
    obtain ⟨hv,hp,he'⟩:= progressed Φ K P S u A L p r T i y h; rw [display]; exact (Uniforms.token (U_ i) (F_ i) (L i.prev) (K_ i) (t_ i.prev) (Geometry.Field.Square.proper _ _) (Z_ i) (Z₀ i) (W₀ i) y₀ r (T.holds i.prev) (poster_h Φ P L p i) hv (Γ.levels.budget (P.vol i.prev)) B (P.upstream Y C Γ K p i) m u hp e he ).symm
lemma checked : R! i.next y' ↔ Task K P S u L p r T i y y' ∧ Able S u m _ y' := by
  have H' := litV Y Φ K P S u A L p r T i y h; have hs:= litW Y Φ K P S u A L p r T i y h; have hv:= twins Y Φ K P S u A L p r T i y h; have he:= stamps Y Φ K P S u A L p r T i y h; constructor
  · rintro ⟨h₁,h₂,h₃⟩; refine ⟨{proper:=fun j hj x=>?_,mark_w:=fun j hj x=>?_},h₁.certified,h₃⟩
    · have hl:= isReal S r (p₁).clip _ _ _ _ h₁ x j hj; exact hl.trans ( congr_fun (hv j hj).symm x )
    change noseC S u (t_ i.next) y' j x= Γm j x; rw [he j hj]; exact h₂.earned j hj x
  rintro ⟨H,Hh⟩; refine ⟨⟨Hh.1,H'.paid,H'.paved,?_⟩,⟨hs.paved,hs.grade,?_⟩,Hh.2⟩
  · intro e ht he x; apply Complex.ofReal_injective; have hh: visible S (p₁).clip (p₁).path (t_ i.next) y' e x= (V_ i.next) e x:= (H.proper e he _).trans (congr_fun (hv e he) x); unfold visible Uniforms.cloth at hh; rw [ if_neg ht.ne', if_neg ht.ne', zero_add ] at hh; rw [Complex.ofReal_neg];exact hh
  intro e ht x; exact (H.mark_w e ht x).trans (congr_fun ((stamps Y Φ K P S u A L p r T i y h) e ht) x)
lemma next : ∃ y': Colors S G (f_ i.next), R! i.next y':= by
    have H' := litV Y Φ K P S u A L p r T i y h; have hs:= litW Y Φ K P S u A L p r T i y h
    have hu : ∃ e l L, (p₁).path.Bounds (p₁).clip e l L := by unfold SeriesT.records; rw [K.selected _ _ _ (P.high C Γ i.next),K.clips _ _ _ (P.high C Γ i.next)]; exact ⟨_,_,_,K.planned.cap _ _ (P.high C Γ i.next)⟩
    obtain ⟨e,l,L',hh⟩:=hu; exact Repop.obtainT S (Z i.next) (W i.next) (t_ i.next) u r m H' hs hh
end See
end YM.RegulatorIR.FVAAlt2.Pipeline
