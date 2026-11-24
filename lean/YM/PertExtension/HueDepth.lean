import YM.PertExtension.PaintLabel

/-! Calibration checked at a shared but possibly larger degree alphabet. -/
set_option autoImplicit false
set_option maxHeartbeats 850000
noncomputable section
namespace YM.PertExtension.Heat.Ray
open Function Set Filter Finset RG Wilson Lattice Labels Source Drops Hue MvPolynomial
open Next.Rank Next.Rank.Beamer Next.Rank.Configuration Next.Rank.LiftMark Next.Rank.Normal Next.Rank.Spindle Top Push.CutoffProjectors Next.Foundations Next.Rank
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge}{d e :ℕ}{F : Labels.Frame G d} (P : poly (Panel RG.Slot G))

lemma cap_depth (h:e≥d) : capRead d (print e P)=clipped d P := by
    rw [← weigh, ← show Rise.trim _ _ d=clipped d P from weigh _,LiftMark.verdict_map d _ (fun i=>(probeX h i).trans (probeX (d:=d) le_rfl i).symm)]
lemma trim_depth {V:Type*}(q:poly V)(w:V→ℕ){e:ℕ}(h:d≤e): Rise.trim (Rise.trim q w e) w d=Rise.trim q w d:=by
  ext i; simp only [Rise.trim_coeff]; by_cases he:Finsupp.weight w i≤e <;> by_cases ht:Finsupp.weight w i≤d <;> try {omega}
  all_goals simp [he,ht]
lemma costs_depth (h:d≤e) :
    let p:=exchange (ink e address) P
    Rise.trim (exchange (features e address 1) P) Configuration.bear d=(rename Sum.inl) (Rise.trim p (key G e) d) :=by
   intro p
   calc
    _ = Rise.trim (Rise.trim (exchange (features e address 1) P) Configuration.bear e) Configuration.bear d:= (trim_depth _ _ h).symm
    _ = (rename Sum.inl) (Rise.trim _ _ d):=by rw [costs,trim_rename];rfl
    _ = _ := congr_arg _ (trim_depth _ _ h)

lemma deep_ink (h:d≤e)(q:Labels.Label G d)(he:clipped d P=q.val) :
    Rise.trim (exchange (features e address 1) P) Configuration.bear d=(rename Sum.inl) (thawKey (raiseLabel G h q)) :=by
    rw [costs_depth _ h];apply congr_arg
    apply rename_injective (R:=ℂ) (f:=(Subtype.val:KeyIn G e→Key G)) (fun i j h=>Subtype.ext h)
    rw [show key G e=generation ∘ Subtype.val from rfl,← trim_rename, returns]; change Rise.trim (print e P) _ _ = _
    exact (weigh _).trans ((cap_depth P h).trans he)
lemma deep_joint (h:d≤e)(hp:Hue.Fixed P) :
    Rise.trim (exchange (features e address 1) P) Configuration.bear d=(rename Sum.inl) (thawKey (raiseLabel G h (F.coords.symm (joint F P)))) :=by
    rw [HueTag.shadow_eq P hp]
    apply deep_ink P h _ rfl
end YM.PertExtension.Heat.Ray
