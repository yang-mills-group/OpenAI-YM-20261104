import YM.Contacts.Sentry.Promise
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Sensor
open Function Set Filter MeasureTheory Extraction Table Org Spec Power Next.UVStress Costar Analysis Ward
open scoped Topology BigOperators ContDiff
variable {G:Gauge} {L:Register G}{ι:Type}[Fintype ι] {S:Table L}(T:Table L)

/-- Linear access. Use quotient multilinear maps for all reader contexts. -/
def measure (x:ι→ E4) (d:ι→ℕ): MultilinearMap ℂ (fun i=> S.Field (d i)) ℂ :=
   let e:= Fintype.equivFin ι
   (MultilinearMap.domDomCongrLinearEquiv' ℂ ℂ (fun i=> S.Field (d i)) ℂ e).symm (classMoment S T (d ∘ e.symm) (points (x ∘ e.symm)))
-- binder `{S}` missing conclusion use measure inferred via v, field notation
lemma measured (x:ι→ E4)(d:ι→ℕ) (v:∀ i,S.Field (d i)) : measure (S:=S) T x d v = corr T x (fun i=>(⟨d i,v i⟩:S.Tag)):=rfl

variable {α:Type*}{P:Pace α}{a:ℝ} [DecidableEq ι]
lemma at_budget (E:ι→ Type*) [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℂ (E i)] [∀ i,FiniteDimensional ℂ (E i)]
   (F:α → MultilinearMap ℂ E ℂ)(hf:∀ x: (∀ i,E i), P.Priced a (fun k=> F k x))
   (p:ι→ℝ) (x:α→ (i:ι)→ E i) (hx:∀ i,P.Priced (p i) (fun k=> x k i)) :
   P.Priced ((∑ i,p i)+a) fun k=> F k (x k):=by
   have hm j s:P.Priced (p j) (fun k=> (Module.finBasis ℂ (E j)).repr (x k j) s):= Pace.Priced.maps (LinearMap.toContinuousLinearMap ((Module.finBasis ℂ (E j)).coord s)) (hx j)
   simp_rw [basis_tuple E (x _)]; apply Pace.Priced.sum; intro i _; exact (Pace.Priced.product Finset.univ (fun j k=>(Module.finBasis ℂ (E j)).repr (x k j) (i j)) p (fun j _=>hm j (i j))).mul (hf (combination E i))

variable {V:Family G}{D:Extraction.Order}{S:Table V.book}(X:Final V D S)(h:Grill V D)
  {μ ℓ:ℝ} (u:ι)(d:ι→ℕ)(T:α→Viewer X)(x:α→ι→ E4)
  (hv: Lit u P x μ ℓ)(hμ:0≤μ)(hℓ:μ≤ℓ)
  (w:α→ (i:ι)→ S.Field (d i))(q:ι→ℝ)(hw:∀ i, P.Priced (q i) (fun k=> w k i))
-- `payroll` in Power includes equation, define cost

def income' (μ ℓ:ℝ):ℝ:=∑ i,(d i:ℝ)* if i=u then μ else ℓ
include h hv hμ hℓ hw
lemma moving : P.Priced ((∑ i,q i) + income' u d μ ℓ) (fun i=> corr (watches X (T i)) (x i) (fun j=>(⟨d j,w i j⟩:S.Tag))):=
   at_budget (fun i=> S.Field (d i)) (fun i=> measure (S:=S) (watches X (T i)) (x i) d) (fun v=> values X h T u x d v hv hμ hℓ) q w hw
-- update single slot charged/others unchanged
end YM.Contacts.Sensor
