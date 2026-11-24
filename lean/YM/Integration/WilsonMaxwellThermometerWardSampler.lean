import YM.Integration.WilsonMaxwellThermometerWardReflection

/-! Put the original independent link Haar variables on the chosen side of each
inversion orbit met by the bulk source. The orientation change on an orbit is
an inversion of its actual Haar link. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerWardSampler
open Function Set Filter MeasureTheory Lattice Wilson PertExtension.Orb
open WilsonMaxwellThermometerWardConditional WilsonMaxwellThermometerWardReflection
open scoped Classical Topology
variable {G:Gauge} {n:Side}

def turn (r:ℕ) (o:Site n) (q:OEdge n) :Prop:= far r o q.val ∧ ¬far r o (reflect q.val)
def pick (r:ℕ) (o:Site n) (q:OEdge n) :Edge (Site n):=
  if turn r o q then reflect q.val else q.val

def orient (r:ℕ) (o:Site n) (q:OEdge n) (a:G.El):G.El:=
  if turn r o q then a⁻¹ else a

def emit (r:ℕ) (o:Site n) (U:Config G n) (q:OEdge n):G.El:=
  orient r o q (U (pick r o q))

theorem anchor (r:ℕ) (o:Site n) (q:OEdge n): index (pick r o q)=q:=by
  apply Subtype.ext
  change eR (pick r o q)=q.val
  unfold pick
  split
  · rw [eR_reflect,q.property]
  · exact q.property

theorem funded (r:ℕ) (o:Site n) : MeasurePreserving (emit (G:=G) r o) (prior G n) (WilsonMaxwellThermometerWardConditional.law G):=by
  let j:=pick r o
  have inj:Injective j:=fun x y h=>(anchor r o x).symm.trans ((congrArg index h).trans (anchor r o y))
  let F:=Equiv.ofInjective j inj
  let D:=MeasurableEquiv.piEquivPiSubtypeProd (fun _:Edge (Site n)=>G.El) (·∈range j)
  have hD:MeasurePreserving D (prior G n) ((WilsonMaxwellThermometerWardConditional.law G).prod (WilsonMaxwellThermometerWardConditional.law G)) :=
    by
      unfold WilsonMaxwellThermometerWardConditional.law
      convert! measurePreserving_piEquivPiSubtypeProd (fun _:Edge (Site n)=>G.probHaar) (·∈range j) using 1
      congr 2; exact Subsingleton.elim ..
  have hS:MeasurePreserving Prod.fst ((WilsonMaxwellThermometerWardConditional.law G).prod (WilsonMaxwellThermometerWardConditional.law G (I:={x//x∉range j})))
      (WilsonMaxwellThermometerWardConditional.law G (I:={x//x∈range j})):=measurePreserving_fst
  have hF:=measurePreserving_piCongrLeft (fun _:OEdge n=>G.probHaar) F.symm
  have chosen:MeasurePreserving (fun U:Config G n=>fun q:OEdge n=>U (j q))
      (prior G n) (WilsonMaxwellThermometerWardConditional.law G):=by
    convert! hF.comp (hS.comp hD) using 1
    funext U q
    obtain ⟨w,rfl⟩:=F.symm.surjective q
    change U (j (F.symm w))=(Equiv.piCongrLeft (fun _:OEdge n=>G.El) F.symm) (fun z=>U z.val) (F.symm w)
    rw [Equiv.piCongrLeft_apply_apply]
    exact congrArg U (congrArg Subtype.val (F.apply_symm_apply w))
  have each (q:OEdge n):MeasurePreserving (orient (G:=G) r o q) G.probHaar G.probHaar:=by
    unfold orient
    by_cases h:turn r o q
    · simp only [h,if_true]; exact Measure.measurePreserving_inv _
    · simp only [h,if_false]; exact MeasurePreserving.id _
  exact (measurePreserving_pi _ _ each).comp chosen

theorem continuous_emission (r:ℕ) (o:Site n):Continuous (emit (G:=G) r o):=by
  apply continuous_pi
  intro q
  unfold emit orient
  by_cases h:turn r o q
  · simp only [h,if_true]; fun_prop
  · simp only [h,if_false]; exact continuous_apply _

theorem received (r:ℕ) (o:Site n) (away:∀e,¬far r o e→far r o (reflect e))
    (U:Config G n) (e:Edge (Site n)) (hot:¬far r o e):liftLinks (emit r o U) e=U e:=by
  by_cases h:eR e=e
  · have hf:¬turn r o (index e):=by simp [turn,index,h,hot]
    rw [liftLinks,if_pos h,emit,orient,if_neg hf,pick,if_neg hf]
    exact congrArg U h
  · have he:eR e=reflect e:=(eR_spec e).resolve_left h
    have hf:turn r o (index e):=by simpa only [turn,index,he,reflect_reflect] using And.intro (away e hot) hot
    rw [liftLinks,if_neg h,emit,orient,if_pos hf,pick,if_pos hf,inv_inv]
    change U (reflect (eR e))=U e
    rw [he,reflect_reflect]

end YM.Integration.WilsonMaxwellThermometerWardSampler
