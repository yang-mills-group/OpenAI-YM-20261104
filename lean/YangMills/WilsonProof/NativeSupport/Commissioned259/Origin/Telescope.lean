import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Patches
/-! # M.4 at the *genuine* physical detector (using the point choice of testing in the proof).
Chosen direction from centre to Far positive time, not negative (we use the example of
`FVA2/O/Read/Point`). Keep reflected-conjugate Far as the detector. The square matrix is
known at Maxwell leading, with uniform/compact phase pricing & Leading, not postulated.
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

variable {d : ℕ} {I : Type} {l:Filter I} {r T s : I → ℝ} (o : I→ E4) (p:I→Viewers F)
-- tables position. centerD for `Probe`; `S=physical`!
open FVA2.O.Read Matrix
lemma framed_entry {n:ℕ}{d:Caps n} (x:Points n) (p:Viewers F)(s:ℝ)(v:Slots G d)(o:E4) (hs:0<s)(hx:x∈conf n) :
    Orbits.moment (spectator F p) (atPosition o s x.ofLp) (enter Z s v)=measured F p (Z s) (d:=d)
      (fun i=> (Free.fields C.labels (d i)).symm (v i)) s x := by
  rw [show atPosition o s x.ofLp=(fun i=> (s • x).ofLp i+o) from funext (fun i=>add_comm ..), Orbits.carrying (y:= (s • x).ofLp) (spectate ..) (Work.A05.smul_conf hs hx), Orbits.observed, named_fin _ (spectate ..).laws.toSymmetric _ (Work.A05.smul_conf hs hx) ]; rfl
lemma maxwell {n:ℕ}{d:Caps n}(C:Family G) (x:Points n) (v:Slots G d): WickGoal (d:=d)
    (fun i=> (Free.fields C.labels _).symm (v i)) x = Wick.moment G x (fun i=> (v i).val) := by
  let f i:=(Free.fields C.labels (d i)).symm (v i); let T:=(Bel C.book)
  change T.useAt T x (fun i=> (⟨d i,f i⟩:T.Tag))=_
  rw [Free.display C.labels _]; congr 1; funext i; unfold f; change (Free.address C.labels _ ((Free.fields C.labels _).symm _))=(v i).val; rw [Free.address_eval,LinearEquiv.apply_symm_apply]

-- at the common s-compact for the pair entries
abbrev Lens (h:ℕ) (v:Viewers F) (o:E4) (s:ℝ) (b:Toon G h) := centerD F Z h (e:=fun (_:Fin 1)=>h) (v,o) s 1 RootG (console 1 b)
-- at the measured exterior r,T
abbrev instrument (h:ℕ) (v:Viewers F) (o:E4) (r T:ℝ) (b: Toon G h) := centerD F Z h (e:=fun (_:Fin 1)=>h) (v,o) r T RootG (console 1 b)
private abbrev focal := forest (0:Points 1) RootG
private lemma focused : focal ∈ conf 2:= ok_wall
private abbrev XI (a:Sec G d) (b:Toon G d) : Slots G (fun _:Fin 2=>d) := Fin.append (fun (_:Fin 1)=>a) (console 1 b)
lemma refraction (v : Owner F) (s:ℝ) (hs:0<s) (a:Sec G d)(b:Toon G d) :
    Lens F Z d v.1 v.2 s b a= Orbits.moment (spectator F v.1) (atPosition v.2 s focal.ofLp) (enter Z s (XI a b)) := by
  let x:=atPosition v.2 s focal.ofLp; have hx:Injective x:=by rw [show x=(fun i=> s • focal.ofLp i+v.2) from funext (fun i=> add_comm ..)]; exact fun i j h=> focused (smul_right_injective _ hs.ne' (add_right_cancel h))
  let t:=spectator F v.1; let z:=enter Z s (XI a b)
  rw [Lens, centerD_apply, mul_one, Orbits.whole_observed,Orbits.observed]
  let f : Fin 1 ⊕ Fin 1≃Fin 2:=finSumFinEquiv
  apply Eq.trans ?_ (perm_observe t (spectate ..).laws.toSymmetric f (Orbits.names z) hx); congr 1
  · funext i; cases i with
    | inl i=> change _= v.2+s • (forest (0:Points 1) RootG _); rw [show f (Sum.inl i)=Fin.castAdd 1 i from rfl,forest_left]; simp
    | inr i=> change _= v.2+s • (forest (0:Points 1) RootG _); rw [show f (Sum.inr i)=Fin.natAdd 1 i from rfl,forest_right]; rfl
  funext i; cases i <;> first| (rename_i j; fin_cases j; rfl) | rfl

-- Actually earn Leading here, no positive-order correlation estimate input.
lemma leading_pair (a b:Toon G d): WickGoal (C:=C) (d:=fun (_:Fin 2)=>d) (fun i=> (Free.fields C.labels d).symm (XI (theory a) b i)) focal = GramP G d b a := by
  rw [maxwell, GramP, focal, RootG,FVA2.O.Enh.lamp, Maxwell.Free.bond_eval]; congr 1; funext i; fin_cases i <;> rfl
private lemma small_room : ∃ M δ:ℝ,0≤M ∧ 0<δ ∧ WithinRoom 1 M δ focal.ofLp 0 := by
  -- suite compact clone already private; explicit pair norms
  refine ⟨1,1,by norm_num,by norm_num,?_⟩; constructor
  · intro i; fin_cases i <;> change ‖_-_‖ ≤ _ <;> simp only [mul_one, sub_zero]; · change ‖(0:E4)‖ ≤ 1; rw [norm_zero]; norm_num
    exact (basis_norm _).le
  intro i j e; fin_cases i <;> fin_cases j <;> simp at e -- closes same; remaining
  · change (1:ℝ)*1≤ ‖(0:E4)-nail‖; rw [zero_sub,norm_neg,nail,basis_norm]; norm_num
  change (1:ℝ)*1≤ ‖nail-(0:E4)‖; rw [sub_zero,nail,basis_norm]; norm_num

include H hZ hQ hq
-- split the enrollment proofs to display the exact phase price before inversion
lemma entitles (hs:Tendsto s l late) (b a:Toon G d) :
    (fun i=>Lens F Z d (p i) (o i) (s i) b (theory a)-Lens F Z d none (o i) (s i) b (theory a))=O[l] fun i=>g0 G (s i)^1 := by
  obtain ⟨M,δ,m,hδ,hM⟩:= small_room
  let u:=XI (theory a) b
  let U i q:=moment (spectator F q) (atPosition (o i) (s i) focal.ofLp) (enter Z (s i) (d:=fun (_:Fin (1+1))=>d) u)
  have hc: Allowance l s s (fun i=> U i (p i)-U i none):= covering F Z Q H hZ hq hQ hs o
    (fun (_:Fin 2) (c:Toon G d)=>Allowance.fixed _) m hδ (Eventually.of_forall fun i:I=> hM) p (fun _=>none) (x:=fun _=> focal.ofLp) (u:=fun _=>u) (d:=fun _=> d)
  refine (flat (sim:=sim) hs 1 hc).congr' ?_ (EventuallyEq.refl ..); filter_upwards [hs.eventually self_mem_nhdsWithin] with i hi
  have hh(q:Viewers F) : Lens F Z d q (o i) (s i) b (theory a) = U i q := refraction F Z (q,o i) (s i) hi (theory a) b
  exact congr_arg₂ (·-·) (hh _).symm (hh _).symm

omit H hQ hq in
lemma committed (hs:Tendsto s l late)(b a:Toon G d): Tendsto (fun i=> Lens F Z d none (o i) (s i) b (theory a)) l (𝓝 (GramP G d b a)) := by
  let V i:= (Free.fields C.labels d).symm (XI (theory a) b i); let u:=XI (theory a) b
  rw [← leading_pair (C:=C) a b]
  refine (PhysMS.leading_at F hZ (d:=fun (_ : Fin 2)=>d) (x:=fun _=> focal) V hs tendsto_const_nhds focused).congr' ?_
  filter_upwards [hs.eventually self_mem_nhdsWithin] with i hR
  exact Eq.symm <| Eq.trans (refraction F Z (none,o i) (s i) hR (theory a) b) (framed_entry F Z focal none (s i) (d:=fun _=>d) u (o i) hR focused)
lemma cleared (hs:Tendsto s l late) : Tendsto (fun i=> Comparing.panel (Lens F Z d (p i) (o i) (s i))) l (𝓝 (GramP G d)) := by
  refine tendsto_pi_nhds.mpr fun b=> tendsto_pi_nhds.mpr fun a=> ?_
  have he:= entitles F Z Q H hZ hq hQ o p hs (d:=d) b a
  have hz:=he.trans_tendsto (show Tendsto (fun i=>g0 G (s i)^1) l (𝓝 0) from by simpa [Function.comp_def] using (g0_zero sim).comp hs)
  exact Tendsto.congr (fun i=> sub_add_cancel (Lens F Z d (p i) (o i) (s i) b (theory a)) (Lens F Z d none (o i) (s i) b (theory a))) (by simpa only [zero_add] using hz.add (committed F Z hZ o hs b a))
end YM.FVA2.GradedFar259.Original
