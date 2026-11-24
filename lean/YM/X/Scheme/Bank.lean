import YM.X.Scheme.Parity
/-!
Parameter incidence: Bank all tests all arities through a horizon,
Section is exactly smear lookups. Restrict honest across horizons.
Define Lie variations and whiteness. Does not by itself enforce any topology.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX
open Pert Pert.Position Maxwell Maxwell.Free Function Set Filter
open scoped Topology Classical BigOperators
variable {G : Gauge} (F: Labels.Frames G) {d e j n : ℕ} (h:d≤e)
abbrev Bank (F : Labels.Frames G) (d : ℕ) := (n:ℕ) → Test n→MultilinearMap ℂ (fun _ : Fin n=> E F d) ℂ
local notation "L" => Buffer F
local notation "U" => up F h
local notation "A" => Bank F

def lookie (s:Pert.Position.Section F d) : Bank F d →ₗ[ℝ] ℂ where
   toFun a:= a s.r s.f s.p
   map_add' x y:= rfl
   map_smul' z x:= rfl
def project (s : Pert.Position.Section F d) := Complex.reCLM.toLinearMap ∘ₗ lookie F s

variable {F}
def pulls (X:E F d →ₗ[ℂ] E F e): Bank F e →ₗ[ℝ] Bank F d where
   toFun a n f:= (a n f).compLinearMap (fun _=> X)
   map_add' _ _:= rfl
   map_smul' _ _:= rfl
lemma pulls_join (X:E F d→ₗ[ℂ] E F e)(M:E F e→ₗ[ℂ] E F j)(v:Bank F j): pulls X (pulls M v)=pulls (M.comp X) v:= rfl
lemma pulls_at {q:Pert.Position.Section F d}(X:E F d→ₗ[ℂ] E F e)(x:A e): lookie F q (pulls X x)=lookie F (d:=e) ⟨q.r,X ∘ q.p,q.f⟩ x:= rfl
variable (F)
@[simp] lemma pulls_same {d}(x:A d): pulls (up F le_rfl) x=x:= by rw [up_same]; rfl
lemma pulls_up (g:e≤j)(x:A j): pulls U (pulls (up F g) x)=pulls (up F (h.trans g)) x:= by rw [pulls_join,show up F g ∘ₗ U=up F (h.trans g) from LinearMap.ext (up_mul F h g)]

lemma pulls_par (x:A e): pulls U (pulls (par F e) x)= pulls (par F d) (pulls U x):= by rw [pulls_join,pulls_join]; exact congr_arg (fun t=>pulls t x) (LinearMap.ext (par_up F h))
lemma pulls_p (x:A d): pulls (par F d) (pulls (par F d) x)=x:= by rw [pulls_join,show par F d ∘ₗ par F d=LinearMap.id from LinearMap.ext (par_cycle F)];rfl

lemma map_update {n} {P Q : Type*}(p:Fin n→P)(i:Fin n)(v:P)(T : P → Q): T ∘ Function.update p i v=Function.update (T ∘ p) i (T v):= by funext j; by_cases h:j=i <;> simp [h]

-- variation at an arbitrary element of orbit (linear on B at given motor)
set_option maxHeartbeats 900000
local notation "S" => Module.End ℂ (E F d)

set_option maxHeartbeats 700000 in
def passB (M:S)(v:A d)(B: S)(i:Fin n) (t:Test n) : MultilinearMap ℂ (fun _ : Fin n=> E F d) ℂ:=by
    let T (j:Fin n): E F d →ₗ[ℂ] E F d:= if j=i then B else M; exact (v n t).compLinearMap T
def profile (M:S)(v:A d)(B:S)(n:ℕ) (t:Test n) : MultilinearMap ℂ (fun _ : Fin n=> E F d) ℂ:= ∑ i:Fin n, passB F M v B i t
lemma letter_val (M:S)(v:A d)(t : Test n)(p:Fin n→E F d)(B:S)(i:Fin n): passB F M v B i t p= v n t (Function.update (M ∘ p) i (B (p i))):= by
   rw [passB,MultilinearMap.compLinearMap_apply]; apply congr_arg _; funext j; by_cases h:j=i<;>simp [h]
lemma profile_val (M:S)(v:A d)(t : Test n)(p:Fin n→E F d)(B:S): profile F M v B n t p=∑ i:Fin n,v n t (Function.update (M ∘ p) i (B (p i))):= by simp only [profile,MultilinearMap.sum_apply,letter_val]

def derivativeBank (M:S)(v:A d) : L d →ₗ[ℝ] A d where
   toFun B:= profile F M v (bufferL F B)
   map_add' x y:= by
      funext n t; ext1 p
      calc
      _ = profile F M v (bufferL F (x+y)) n t p:=rfl
      _ = profile F M v (bufferL F x) n t p + profile F M v (bufferL F y) n t p:= by
            simp only [profile_val,bufferL_eq,show ∀ q:E F d,(x+y).val q=x.val q+y.val q from fun _=> rfl, MultilinearMap.map_update_add,Finset.sum_add_distrib]
      _ = _:= rfl
   map_smul' r x:= by
      funext n t; ext1 p
      calc
      _ = profile F M v (bufferL F (r • x)) n t p:=rfl
      _ = r • profile F M v (bufferL F x) n t p:= by
            rw [profile_val,profile_val,Finset.smul_sum]; simp only [bufferL_eq]; apply Finset.sum_congr rfl; intro i hi; exact ((v n t).restrictScalars ℝ).map_update_smul _ _ _ _
      _ = _:= rfl

def pureBank (F:Labels.Frames G) (d:ℕ):Bank F d:= fun _=>wickReading F d

def jacBank (v:A d):= derivativeBank F LinearMap.id v
lemma jacBank_eval (v:A d)(s : Pert.Position.Section F d)(x:L d): lookie F s (jacBank F v x)=∑ i:Fin s.r,v s.r s.f (Function.update s.p i (x.val (s.p i))):= profile_val F LinearMap.id v s.f s.p (bufferL F x)
lemma jacBank_zoom (v:A e)(x:L e): jacBank F (pulls U v) (zoomL F h x) = pulls U (jacBank F v x):= by
   funext n t; ext1 p; let q : Pert.Position.Section F d:= ⟨n,p,t⟩; change lookie F q (jacBank F (pulls U v) (zoomL F h x))= lookie F q (pulls U (jacBank F v x)); rw [pulls_at,jacBank_eval,jacBank_eval]; apply Finset.sum_congr rfl; intro i hi; change v n t (U ∘ Function.update p i _)=v n t _; rw [map_update,zoomL_eq]; rfl
lemma jacBank_par (v:A d)(x:L d): jacBank F (pulls (par F d) v) (cPar F x)=pulls (par F d) (jacBank F v x):= by
   funext n t; ext1 p; let q : Pert.Position.Section F d:= ⟨n,p,t⟩; change lookie F q (jacBank F (pulls (par F d) v) (cPar F x))=lookie F q (pulls (par F d) (jacBank F v x)); rw [pulls_at,jacBank_eval,jacBank_eval]; apply Finset.sum_congr rfl; intro i hi; change v n t (par F d ∘ Function.update p i _)=v n t _; rw [map_update, cPar_eq, par_cycle]; rfl
lemma pureJac (s:Pert.Position.Section F d)(x:L d): project F s (jacBank F (pureBank F d) x) = feedback F d s x:= by rw [feedback_eq]; change Complex.re (lookie _ _ _) = _; rw [jacBank_eval]; rfl
lemma pure_zoom : pulls U (pureBank F e)=pureBank F d:= by
   funext n t; ext1 p; change (wickReading F e t) (U ∘ p)= (wickReading F d t) p
   apply congr_arg (Test.applyTo t); funext z; rw [visible_eq F,visible_eq F]; exact congr_arg _ (funext fun i=> address_rise F _ h (p i))
end YM.PositionX
