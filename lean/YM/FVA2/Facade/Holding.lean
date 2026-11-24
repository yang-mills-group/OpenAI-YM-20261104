import YM.FVA2.Facade.Cash
/-!
 # Joint conditional history in inversion regulator

 Coordinates: freeze **all** coarse link orbits at `Bottom L` (the FULL fields; not
 just projecting to any future terminal tree, no choice of tree necessary there).
 `Panel` keeps exactly the off-interior-tree fields at every earlier level. `Drive`
 transports polynomials through such a prefix; it's exactly RG10. There's no mandatory
 difference in period between it and this prefix ordinary-Gaussian rule.

 The floor is included as a terminal where one *can* apply the final tree, e.g.
 for the terminal expectation after all the conditional evaluations. But there will be no reference to that floor tree in these operations.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Facade
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter MeasureTheory PertExtension Precision Lattice GaussianScore PowerSeries Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open scoped Classical Topology BigOperators ContDiff ENNReal
variable {G: Gauge} {c f n:Side}

 def Bottom {n : Side}(L:Fabric G n) : Side:= match L with
 | .endcap k _=> k
 | .layer _ _ _ _ L=>Bottom L

 def Warm {n:Side}{L:Fabric G n}(T:Cloth L) : Type := match T with
 | .floor _ _ _=> Empty
 | .inLayer (S:=S) P C=> Blocking.Index S P ⊕ Warm C
@[implicit_reducible] def iWarm {n:Side}{L:Fabric G n}(T:Cloth L) : Fintype (Warm T):= by
 cases T with
 | floor => unfold Warm; infer_instance
 | inLayer P C => letI:= iWarm C; unfold Warm; infer_instance
termination_by structural T
attribute [instance] iWarm

variable {L:Fabric G n} (T:Cloth L)
abbrev Panel := Warm T→ G.Color
abbrev Entry:= Panel T × Flats G (Bottom L)

section
variable {S: StepData c f}{U:Fabric G c} {H:S.patch.Branches S.kernel G}{hf: Even f.val}{t:S.Choices}{P:Inside S.ratio}{C:Cloth U}
local notation "T0"=> Cloth.inLayer (t:=t) (b:=H) (h:=hf) P C
local notation "F"=> Cross (G:=G) S P
local notation "B"=> Panel C
local notation "Y"=> Flats G (Bottom U)
local notation "E"=> Panel T0

def credit : (F×B) ≃ₗ[ℝ] E where
 toFun u i:= Sum.elim u.1 u.2 (show Blocking.Index S P⊕Warm C from i)
 invFun x:= ((fun i=> x (Sum.inl i : _⊕Warm C)),fun i=>x (Sum.inr i : Blocking.Index S P ⊕_))
 left_inv _ := rfl
 right_inv a:= by funext i; change Blocking.Index S P⊕Warm C at i; cases i<;> rfl
 map_add' _ _:= funext fun i=> by change Blocking.Index S P⊕Warm C at i; cases i<;> rfl
 map_smul' _ _:= funext fun i=> by change Blocking.Index S P⊕Warm C at i; cases i<;> rfl
local notation "Ξ" => credit (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)

 def tollFirst : Entry T0→ₗ[ℝ] F:= (LinearMap.fst ℝ F B) ∘ₗ (Ξ).symm.toLinearMap ∘ₗ LinearMap.fst ℝ E (Flats G (Bottom (layer S H t hf U)))
 def descend : Entry T0→ₗ[ℝ] Entry C:= ((LinearMap.snd ℝ F B) ∘ₗ (Ξ).symm.toLinearMap).prodMap (LinearMap.id (R:=ℝ) (M:=Y))
local notation "T'"=> tollFirst (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)
local notation "π"=> descend (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)
@[simp] lemma chargedFirst (x y u) : T' (Ξ (x,y),u)=x:= by simp [tollFirst]
@[simp] lemma descending (x y u) : π (Ξ (x,y),u)=(y,u):= by simp [descend]; rfl
end

 def line {n:Side}{L:Fabric G n}(T:Cloth L): Entry T→ₗ[ℝ] Flats G n:= match T with
 | .floor k h B=> (LinearMap.snd ℝ (Panel (Cloth.floor k h B)) (Flats G k))
 | .inLayer P _=> extend P ∘ₗ tollFirst

section Cells
variable {S: StepData c f}{U:Fabric G c} {H:S.patch.Branches S.kernel G}{hf: Even f.val}{t:S.Choices}{P:Inside S.ratio}{C:Cloth U}
local notation "T0"=> Cloth.inLayer (t:=t) (b:=H) (h:=hf) P C
local notation "T'"=> tollFirst (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)
local notation "Ξ" => credit (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)
 def arrows : Entry T0→ₗ[ℝ] (Cross (G:=G) S P) × Flats G c:= (T').prod (line C ∘ₗ descend)
@[simp] lemma arrived (x y u) : arrows (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C) (Ξ (x,y),u)=(x,line C (y,u)):= by simp [arrows]; rfl
@[simp] lemma lined (x y u) : line T0 (Ξ (x,y),u)= extend P x:= by unfold line; simp
end Cells

 def valve {n : Side}{L:Fabric G n}(T:Cloth L)(i:L.Cost) : Entry T→ ℝ := match T with
 | .floor _ _ _=> Empty.elim i
 | .inLayer (t:=t) P C=> Option.elim i (substep P t ∘ arrows) (fun a=> valve C a ∘ descend)
lemma valved {n:Side}{L:Fabric G n}(T:Cloth L)(i:L.Cost) : ContDiffAt ℝ ω (valve T i) 0:= by
 cases T with
 | floor=> exact Empty.elim i
 | @inLayer c f S b t hf L P C=> change Option L.Cost at i; cases i with
                               | none=> exact leaned arrows (subReady P t b)
                               | some i=> exact leaned descend (valved C i)
termination_by structural T

variable (z:L.Cost→PowerSeries ℝ)
 def totalPrice {ι:Type}[Fintype ι]{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](p:ι→Quadratic E): Quadratic E where
 P:=∑ i,(p i).P
 side x y:=by simp [(p _).side]
lemma bought {ι:Type}[Fintype ι]{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](p:ι→Quadratic E)(x:E): (totalPrice p).flourish x=∑ i,(p i).flourish x:= by unfold totalPrice flourish; simp

-- pure penalty bill (from actual block costs with arbitrary top-variable coupling schedule)
 def unpaid: Quadratic (Entry T):= totalPrice (fun i:L.Cost=> Quadratic.genesis (z i) (valve T i))
 def packed : Ticket (Entry T):= ∏ i, chip (z i) (valve T i)

 def pending (J:ChartRatio G) : Ticket (Entry T):= packed T z* boost (LinearMap.fst ..) (tissue J (Warm T))
-- allow unmasked inputs, from top.Read never carries paid inverse dets for them
 def policy (U:Unmasked G n): Quadratic (Entry T):= addOn (drag (line T) U.Q) (unpaid T z)
 def ledge (J:ChartRatio G)(U:Unmasked G n): Ticket (Entry T):= boost (line T) U.W * pending T z J

lemma reserve (U:Unmasked G n)(J:ChartRatio G)(h:LocalRatio J)(u:incline U.W): incline (ledge T z J U):= by
 unfold ledge; apply pool (preserve_boost _ u); unfold pending; apply pool _ (preserve_boost _ (awake h))
 unfold incline packed; simp_rw [map_prod, show ∀i:L.Cost, constantCoeff (chip (z i) (valve T i))=1 from fun i=> OpenSlots.restores ..]; simp

end YM.FVA2.Facade
