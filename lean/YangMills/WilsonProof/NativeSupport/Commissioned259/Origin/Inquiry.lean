import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Receive
/-! # G.6 first inequality and phase powers, on the measured fields H (every vector)

Get all families, once the original LogTrace on this Reader and the indicated QScale
purchases obtained. No `Budget` from the exact claim about the fields being tested. Allows
all T with positive room margins, rather than just T power in g⁻¹.
-/
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
local notation "U" => (fun i=>enter Z (r i) (u i))
local notation "V" => (fun i=>enter Z (s i) (v i))
local notation "P" i:max => spectator F (p i)
local notation "z" i:max => atPosition (o i) (r i) (x i)
local notation "z'" i:max => atPosition (o i) (s i) (y i)
local notation "Qₕ" i:max u:max => Q.packet h (z i) u (o i)
local notation "wage" => (fun i:J=> s i + (r i/s i)^(h+1))
local notation "wΩ" i:max d:max e:max => r i^(∑ j,d j)*s i^(∑ j,e j)

include H hZ hq hs hx hu hv
-- collaboration of two payments. take a paired family if one truly MLA in each set of arguments
lemma together {E : Type*} [NormedAddCommGroup E][NormedSpace ℂ E] (f:J→ℝ)
    (D: J→ Orbits.Labels S d→Oper (E:=E) S e) (B:J→Orbits.Labels S e→ Oper (E:=E) S d)
    (he: ∀ᶠ i in l,∀ u v,D i u v=B i v u)
    (pay:∀ d' e' (h:d'≤ d) (q:e'≤ e) (u:Labels S d') (v:Labels S e'),Allowance l r (fun i=> f i/(wΩ i d' e'))
      (fun i=> D i (promote F h u) (promote F q v))) : Allowance l r f (fun i=> D i (U i) (V i)) := by
  have hr:= smaller_radius hs hx
  refine (receiving F Z H hZ hq hr hr (Eventually.of_forall fun _=>le_rfl) d (fun i=> B i (V i)) u (w:=f) ?_ hu).congr (he.mono fun i h=> (h _ _).symm)
  intro d' h u
  refine (receiving F Z H hZ hq hr hs (hx.mono fun i h=>h.adj) e (fun i=> D i (promote F h u)) _ ?_ hv).congr (he.mono fun i h=>h _ _)
  intro e' q v
  exact (pay _ _ h q u v).extend (Eventually.of_forall fun _=>(div_div ..).symm)
include hQ mn dp
lemma paid_discrepancy : Allowance l r wage (fun i=> discrepancy (P i) h (z i) (o i) (U i) (Qₕ i (U i)) (z' i) (V i)) := by
  let D i w := distance (S:=S) (P i) (z i) w (d:=d) h (Qₕ i w) (o i) (z' i) (e:=e)
  let B i w := local_disc (S:=S) (P i) (z i) h (packetN Q (z i) (o i) h) (z' i) w (o i) (e:=e) (d:=d)
  simp_rw [far_distance]
  refine together F Z H hZ hq hs hx hu hv wage D B ?_ ?_
  · apply Eventually.of_forall; intro i u v; unfold D B; rw [ ← far_distance, ← location,packetN_eq Q]
  intro d' e' hi j v k
  refine (currency F Q sim (Z 0) mn dp hQ v k p hs hx h (o:=o)).congr ?_
  filter_upwards [hx] with i live; unfold D; rw [← far_distance, packet_rises F Q hi]; unfold discrepancy; apply congr_arg₂ (·-·)
  · rw [lite F _ (profiles (o i) live dp), far_lite F _ (profiles _ live dp)]
  exact (far_lite (d:=e') (c:=fun _=>h) F _ (center_profiles _ live dp) j (fun _=>Qₕ i v) k).symm

lemma split_phase (q:J→Viewers F) : Allowance l r s (fun i=> Orbits.whole (P i) (z i) (U i) (z' i) (V i)- Orbits.whole (spectator F (q i)) (z i) (U i) (z' i) (V i)) := by
  let D (i) (u: Labels S d) := whole₁ (P i) (z i) (z' i) (e:=e) u - whole₁ (spectator F (q i)) (z i) (z' i) u
  -- Near cost needs sectionally MLA
  let B (i) (v: Labels S e) := (show Oper (E:=ℂ) S d from sectionLabels v (moment (P i) (d:=Sum.elim d e) (beside (z i) (z' i)))) -
      (show Oper (E:=ℂ) S d from sectionLabels v (moment (spectator F (q i)) (d:=Sum.elim d e) (beside (z i) (z' i))))
  have he (i) (u:Labels S d) (v:Labels S e) : D i u v=Orbits.whole (P i) (z i) u (z' i) v-Orbits.whole (spectator F (q i)) (z i) u (z' i) v := by simp_rw [whole₁_eq]; rfl
  simp_rw [ ← he ]; refine together F Z H hZ hq hs hx hu hv s D B ?_ ?_
  · refine Eventually.of_forall fun i u v=> Eq.trans (he i u v) ?_; unfold B Orbits.whole; erw [MultilinearMap.sub_apply,sectionLabels_apply,sectionLabels_apply]
  intro d' e' hi j u v
  refine (prime F Q sim (Z 0) mn dp hQ u v p (o:=o) hs hx q).congr ?_
  filter_upwards [hx] with i live; have hp:=profiles (o i) live dp; rw [he]; simp_rw [lite F _ hp _,far_lite F _ hp _]
end YM.FVA2.GradedFar259.Original
