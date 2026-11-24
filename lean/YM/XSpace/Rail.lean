import YM.XSpace.Offset

/-!
# Separated external vertex train (any locations)
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Stall
open Function Filter Set Lattice Mu Trace Shade Chart2 MvPolynomial Next.Rank.Normal Contraction Finsupp Future JetGauge Drama
open scoped Topology BigOperators ContDiff
variable {ι V T:Type} {G:Gauge} {L:Filter ι} {k d:ℕ}

-- send each mark in scaled Hartree-current form to all circuits
variable (x:ι→Cover) (a:ι→ℝ)
def Calling (p:Fee G)(i:ι): Line G:= (a i)⁻¹^ p.cost • displace (x i) p.line
def reading (p:Stamp G)(t:ℕ)(i:ι):= tick a i t • Trace.volume (x i) p

def chain (C:ι→ℂ)(p:ι→Stamp G)(i:ι):Stamp G:=C i • p i
def pencil (p:ι→Line G)(i:ι):= harp (p i)
lemma harp_weights (L:Line G)(a:ℝ) : harp (a • L)=(a:ℂ) • harp L:=by apply same; intro A; rw [leg_test,map_smul,map_smul (pit A), leg_test, LinearMap.smul_apply]; simp

inductive Records (a:ι→ℝ)(L:Filter ι)(x:ι→Cover): (ι→Stamp G)→Prop where
| unit: Records a L x 1
| zero: Records a L x 0
| scale {A}: Records a L x A → ∀ c:ι→ℂ,Likely L c→Records a L x (chain c A)
| add {A B}: Records a L x A→ Records a L x B→ Records a L x (A+B)
| receive (h:Fee G)(s:Stops h.line){A}: Records a L x A → Records a L x (pencil (Calling x a h)*A)
namespace Records
lemma program {p:Stamp G}(h:p∈ OnStage G d): Records a L x (reading x a p d):=by
  induction h using Submodule.span_induction with
  | mem u hx=> obtain ⟨M,hM,rfl⟩:=hx; rw [← hM.1]; have hh:=hM.2; clear hM; induction M with
               | nil=> rw [show Stall.reading x a (story ([]:Word G)) (debt [])=1 from funext fun j=> by simp [Stall.reading,debt,tick]]; exact Records.unit
               | cons i M ih=>
                 have he: reading x a (story (i::M)) (debt (i::M))=pencil (Calling x a i)*reading x a (story M) (debt M):=by
                   funext j; unfold reading Calling pencil tick; rw [inc,read_word,map_mul,rings,Pi.mul_apply,harp_weights,smul_mul_smul,pow_add];push_cast;rfl
                 rw [he]; exact Records.receive _ (hh _ (by simp)) (ih fun i hi=>hh _ (by simp [hi]))
  | zero=> rw [show Stall.reading x a (0:Stamp G) d=0 from funext fun i=>by simp [Stall.reading]]; exact Records.zero
  | add p q _ _ i j=> rw [show Stall.reading x a (p+q) d=Stall.reading x a p d+Stall.reading x a q d from funext fun k=>by simp [Stall.reading,smul_add]]; exact Records.add i j
  | smul t u _ IH=> rw [show reading x a (t • u) d=chain (fun _=> t) (reading x a u d) from funext fun i=> by unfold reading chain; rw [map_smul,smul_comm t]]; exact Records.scale IH _ (Likely.const ..)
-- closure under every derivative along a *cross* signal. Does not hold along same-slot; skip price then.
variable {x a}
def strike (B:ι→ Contact G)(p:ι→Stamp G)(i:ι):= D (B i) (p i)
lemma biting {B:ι→Line G}{p:ι→Stamp G}(X:Records a L x p)(h:∀ f:Fee G, Stops f.line → Likely L fun i=>(handshake (B i) (Calling x a f i):ℂ)) : Records a L x (strike (fun i=>bake (B i)) p):= by
  induction X with
  | unit=>unfold strike; simp only [Pi.one_apply]; simp_rw [Derivation.map_one_eq_zero]; exact Records.zero
  | zero=> unfold strike; simp only [ Pi.zero_apply,map_zero]; exact Records.zero
  | scale h c hp ih=> unfold strike; simp_rw [ chain,(D _).map_smul]; exact Records.scale ih c hp
  | add a b i j=> unfold strike; simp only [Pi.add_apply,map_add]; exact Records.add i j
  | @receive f s A X ih=> unfold strike; simp only [Pi.mul_apply, pencil,(D _).leibniz, played,smul_eq_mul]; change Records _ _ _ (fun i=>_*_+A i*C (handshake (Calling x a f i) (B i):ℂ)); simp_rw [mul_comm (A _),C_mul',listening (Calling x a f _)]; exact Records.add (Records.receive _ s ih) (Records.scale X _ (h f s))
end Records
end YM.XSpace.Stall
