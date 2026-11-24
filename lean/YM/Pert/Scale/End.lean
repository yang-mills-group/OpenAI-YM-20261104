import YM.Pert.Parity.End
import YM.Pert.Scale.Return
import YM.Pert.Scale.ReadPatch
import YM.Pert.Scale.Slope
/-!
A local-in-length relative branch on the *same* Wilson extraction as `firstTarget`, with explicit separated leading scale (including inverse-label step, engineering derivative, physical stress read-back at horizon four). No bound after returning to scale-independent reference fields.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Pert.Scale
open Position Maxwell Parity Extra.FD RawLabels Ward Climb Function Filter Topology Spec
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {C : Family G} {I : Extraction.Order} {S : Table C.book} {n : ℕ} {Q : Conditions C.labels 4 n}
structure Patch (b:Final C I S) (X:Scaling S) (φ : Ledger Q→Buffer C.labels 4) : Prop where
  exactTests {t:ℝ} (ht : 0<t) : ∀ᶠ v : ℕ×ℝ in atTop ×ˢ 𝓝 t, Cleared X φ v.1 v.2 ∧ actualTest Q X φ v.1 v.2=chart Q (white Q,0)
  subgroup {t:ℝ} (ht : 0<t) : ∀ᶠ v : ℕ×ℝ in atTop ×ˢ 𝓝 t, YM.Spin.realH b.room.kernel.spin (Free.spin_free _) (positionScale X φ v.1 v.2) ∧
      positionScale X φ v.1 v.2 ((freeTable C.labels).unit 4)=S.unit 4 ∧ ∀ d (hd:d<4) p, positionScale X φ v.1 v.2 (toFour C.labels hd.le p) = b.sector.derivatives.rise hd.le (X.U v.1 d p)
  readings (s : ℝ) (hs:0<s) (m) (R : Conditions C.labels 4 m) (hr : CleanProfiles R) : Tendsto (fun i : ℕ×ℝ=>actualTest R X φ i.1 i.2) (atTop ×ˢ 𝓝 s) (𝓝 (chart R (white R,0))) ∧
     Tendsto (fun k=>deriv (actualTest R X φ k) s) atTop (𝓝 0)
  diagrams (s : ℝ) (hs:0<s) (m) (R : Conditions C.labels 4 m) (hr : CleanProfiles R) (L : Lattice.Side) (hL : 1<L.val) (p : ℕ) :
      Tendsto (fun k=>actualTest R X φ k s - readJet φ p 0 (chart R) (finite Q L k) (finite R L k)) atTop (𝓝 0)
  steps (s t : ℝ) (hs:0<s) (ht:0<t) (p) :
     Tendsto (fun k : ℕ => (positionScale X φ k s).symm ((positionScale X φ k t) p)) atTop (𝓝 (gear C.labels 4 (t/s) p))
  engineer (s : ℝ) (hs:0<s) (i) : let B := recorded C.labels 4
     Tendsto (fun k=>s • deriv (fun t:ℝ=>(positionScale X φ k s).symm (positionScale X φ k t (B.b i))) s) atTop (𝓝 ((B.w i).1 • B.b i))
  angular (s : ℝ) (hs : 0<s) (i : Axis × Axis) (v : E C.labels 4) :
   Tendsto (fun k : ℕ => YM.Spin.transport b.sector.turns.lie (positionScale X φ k s) i v) atTop (𝓝 ((gearIso C.labels 4 s hs).symm (dressedLie _ 4 i s v)))
  tensor (i j) (s : ℝ) (hs:0<s) :
    Tendsto (fun k : ℕ => (positionScale X φ k s).symm ((↑((s*X.r k)^4:ℝ):ℂ) • b.sector.energy i j)) atTop (𝓝 (freeStress C.labels i j))

variable {b : Final C I S} {X : Scaling S} {φ : Ledger Q→Buffer C.labels 4}
lemma patch_ready (hg : G.Simple) (h : FirstExtension b X) (hq:CleanProfiles Q) (hl:Reports (chart Q) (white Q) 0 φ) : Patch b X φ := by
  refine ⟨fun ht=>(clearance h hq hl ht |>.mono fun _ h=>h.1).and (actual_fixed h hq hl ht), fun ht=>?_,fun s hs m R hr=> ⟨response_limit h hq hl R hr hs,response_turns h hq hl R hr hs⟩,
    fun s hs m R hr L hL p=> ?_, step_limit h hq hl,fun s hs i=>length_slope h hq hl hs i,turn_limit h hq hl,fun i j s=> measured_stress h hq hl i j⟩
  · have hi : ∀ᶠ k in atTop, ∀ i : Fin 4, ∀ p, X.U k 4 ((Free.scheme C.labels).rise i.isLt.le p) = b.sector.derivatives.rise i.isLt.le (X.U k i p) :=
       eventually_all.mpr (fun i=>h.fit.rises i 4 i.isLt.le)
    filter_upwards [((h.fit.hsym 4).and (h.fit.units 4)).prod_inl (𝓝 _),clearance h hq hl ht,hi.prod_inl (𝓝 _)] with v hv hc hr
    refine ⟨position_symmetric (b:=b) hv.1 hc.1, (congrArg (X.U v.1 4) (relative_unit hc.1)).trans hv.2,fun d hd p=> ?_⟩
    rw [pos_eq X hc.1,motor_small C.labels hg hd]
    obtain ⟨a,rfl⟩ := UVNext.FreeStress.below C.labels hg hd p
    have hkeep := (Free.scheme C.labels).fixs (Free.scheme_filters C.labels) (table_regular _) hd.le
    rw [toFour,map_smul,hkeep,map_smul,gear_unit]
    have he := hr ⟨d, hd⟩ (a • (freeTable C.labels).unit d)
    simp only [map_smul,hkeep] at he ⊢
    exact he
  simp_rw [← continuous_jet R L _ p]
  let y := chart R (white R,0)
  have he : Tendsto (fun k => actualTest R X φ k s) atTop (𝓝 y) := fixed_stitch (response_limit h hq hl R hr hs)
  have hy : Tendsto (renormLeading φ R L) atTop (𝓝 y) := by
     have htL := (finite_leading R hr L hL).prodMk_nhds ((ContDiffAt.continuousAt hl.diff).tendsto.comp (finite_leading Q hq L hL))
     rw [hl.fixes] at htL
     exact ((chart_diff R).continuous.tendsto _).comp htL
  simpa only [sub_self] using he.sub hy

/-- Public current endpoint for exact relative position frames at horizon four; does not assert coverage of all absolute scales, perturbative-order remainders beyond zeroth, OPE-array comparison or construction of the nontrivial coupling. No assumption of matching on Wilson reports. -/
theorem scaleEndpoint (hg : G.Simple) {c : ℝ} (hc : 0<c) : ∃ C : Family G,
  C.path.levels.clock.kernel.penalty=c ∧ Extraction.Wcmain C ∧ MergeProof.Ribbons.Materials C ∧ MergeProof.Ribbons.Plenty C ∧
   ∀ f : Extraction.Order, ∃ (g : Extraction.Order) (S : Table C.book) (b : Final C (f.refine g) S), ∃ X : Scaling S, FirstExtension b X ∧ Crest X ∧ ∃ (n : ℕ) (Q : Conditions C.labels 4 n) (φ : Ledger Q→ Buffer C.labels 4) (J : Module.End ℝ (Fin n→ℝ)), CleanProfiles Q ∧ BoardAttains Q X φ ∧ Resident b X φ ∧ Fair Q J ∧ ParityFields φ ∧ Patch b X φ := by
  obtain ⟨C,hc0,hW,hM,hP,H⟩ := parityEndpoint hg hc
  refine ⟨C,hc0,hW,hM,hP,fun f => ?_⟩
  obtain ⟨g,S,b,X,hX,hC,n,Q,φ,J,hq,hf,hr,hj,hp⟩ := H f
  exact ⟨g,S,b,X,hX,hC,n,Q,φ,J,hq,hf,hr,hj,hp,patch_ready hg hX hq hf.toMode.patch⟩

end YM.Pert.Scale
