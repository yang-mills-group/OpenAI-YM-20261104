import YM.X.Reed.Ahead
import YM.X.Stems.Bob
/-!
`K=d₁ᵀd₁`-null polynomial 1-form test. Off-shell longitudinal tests allowed without divergence-free condition. Periodic translated cover linear map K; Taylor curvature used for CT. Degree is m (weight m+1).
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Reed
open Lattice Wilson Stems Next.Rank.CellsInt Tensor TensorProduct Filter MeasureTheory Metric Finset Function Maxwell
open scoped Topology ContDiff BigOperators
variable {G:Gauge} {V : Type} [NormedAddCommGroup V][NormedSpace ℝ V] {n:ℕ}
def raising (j:Axis):Brush G→ₗ[ℝ] Cover→G.Color:= LinearMap.pi (fun x=>LinearMap.proj (x,j))
def curlL (i j:Axis): Brush G→ₗ[ℝ] Cover→G.Color where
   toFun A:= stepValue (raising j A) i - stepValue (raising i A) j
   map_add' A B:= by simp only [map_add,Next.Rank.Beamer.step_add]; abel
   map_smul' r A:= by
      have he (f:Cover→G.Color)(i:Axis):stepValue (r • f) i=r • (stepValue f i):= jumps_scale 1 (fun _=>i) f r; simp only [map_smul,he,RingHom.id_apply,smul_sub]
lemma curling (A:Brush G)(i j:Axis)(z:Cover): curlL i j A z=curl A z i j:= by change (A (z+step i,j)-A _)-(A (z+step j,i)-A _)=_; unfold curl; abel
def rewinds (i:Axis): (Cover→V) →ₗ[ℝ] Cover→ V where
   toFun f:= rewind f i
   map_add' f g:=by funext z; exact congr_fun (Next.Rank.Beamer.step_add ..) _
   map_smul' r f:= by funext z; exact congr_fun (jumps_scale 1 (fun _=>i) f r) (z-step i)
def orderK (j:Axis): Brush G→ₗ[ℝ] Cover→G.Color:= -(∑ i:Axis,(rewinds i) ∘ₗ (curlL i j))
def evenShape (n:ℕ):Submodule ℝ (Axis→T E4 G.Color n):= Submodule.pi Set.univ (fun _=> {carrier:={A|Tensor.Sym A},zero_mem':=fun _ _=>rfl,add_mem':=fun {_ _} ha hb v s=> congr_arg₂ HAdd.hAdd (ha v s) (hb v s), smul_mem':=fun a _ h v s=> congr_arg (a • ·) (h v s)}) -- inspect
abbrev Specs (G:Gauge)(n:ℕ):= ↥(evenShape (G:=G) n)
lemma Specs.sym (p:Specs G n)(i:Axis):Tensor.Sym (p.val i):= p.property i (by simp)
def skew (n:ℕ): (Axis→T E4 G.Color n) →ₗ[ℝ] Brush G:= LinearMap.pi (fun i=>(LinearMap.proj i.1) ∘ₗ (reach (tip i.2)) ∘ₗ (LinearMap.proj i.2))
def trot : (Axis→ T E4 G.Color (n+1)) →ₗ[ℝ] TwoJet G.Color n:= LinearMap.pi fun i:Axis=> LinearMap.pi fun j:Axis=> (burst i) ∘ₗ (LinearMap.proj j) - (burst j) ∘ₗ (LinearMap.proj i)
lemma trot_achieves (p:Specs G (n+1))(i j:Axis) : curlL i j (skew _ p.val)=reach (tip i+tip j) (trot p.val i j) := by
     change stepValue (reach (tip j) (p.val j)) i- stepValue (reach (tip i) (p.val i)) j=reach (tip i+tip j) (burst i (p.val j)-burst j (p.val i)); rw [step_grabs (p.sym _),step_grabs (p.sym _),add_comm (tip j),map_sub]
lemma trot_secure (A: Brush G) : Secure (fun i j=> curlL i j A):= by
     let p(i:Axis)(j:Axis):=stepValue (raising j A) i
     have ht(i:Axis)(f g:Cover→G.Color) : stepValue (f-g) i= stepValue f i-stepValue g i:= jumps_sub 1 (fun _=>i) f g
     constructor
     · intro i j; change p i j- p j i= - (p j i-p i j); abel
     intro a b c; change stepValue (p b c-p c b) a+ stepValue (p c a-p a c) b+stepValue (p a b-p b a) c=0; simp only [ht,p]; rw [hop b a,hop c a,hop c b]; abel
lemma trot_sym (p:Specs G (n+1))(i j:Axis): Tensor.Sym (trot p.val i j):= fun v s=> congr_arg₂ HSub.hSub (burst_sym (p.sym j) i v s) (burst_sym (p.sym i) j v s)
lemma trot_closed (p:Specs G (n+1)) : Maxwell.ClosedJet (trot p.val) := by
     have he:trot p.val=leaf n (fun i j=> curlL i j (skew _ p.val)):= by
        funext i j; apply seedEq; intro v; simp only [leaf,fertile,trot_achieves,PositionX.Reed.top (trot_sym p i j),smul_smul,inv_mul_cancel₀ (show (n.factorial:ℝ)≠0 by positivity),one_smul]
     rw [he]; exact sprout n (trot_secure _)

def heat (j:Axis): TwoJet V (n+1) →ₗ[ℝ] T E4 V n:= ∑ i:Axis,(burst i) ∘ₗ (LinearMap.proj j) ∘ₗ (LinearMap.proj i)
lemma heat_apply (j)(X: TwoJet V (n+1)): heat j X=∑ i:Axis, burst i (X i j):= by simp [heat]
lemma heat_sym (j)(X:TwoJet V (n+1))(h:ClosedJet X): Tensor.Sym (heat j X):= by rw [heat_apply];intro v s; simp only [_root_.sum_apply]; exact sum_congr rfl (fun i _=> burst_sym (h.coeffSym i j) i v s) -- metavars
lemma heat_K (p:Specs G (n+2))(j:Axis): orderK j (skew _ p.val)=reach (tip j) (-heat j (trot p.val)):= by
    simp only [orderK, LinearMap.neg_apply, LinearMap.sum_apply, LinearMap.comp_apply,trot_achieves,heat_apply,map_neg,map_sum]; apply congr_arg; apply sum_congr rfl; intro i _; change rewind (reach _ _) i=_; rw [rewind_grabs (trot_sym p i j),add_sub_cancel_left]
lemma heat_low (p: Specs G 1)(j:Axis): orderK j (skew _ p.val)=0:= by
    rw [orderK, LinearMap.neg_apply, LinearMap.sum_apply]; apply neg_eq_zero.mpr; apply sum_eq_zero; intro i _; rw [LinearMap.comp_apply,trot_achieves,reach0 _ _ Fin.elim0]; funext z; change _-_=(0:G.Color); exact sub_self _
lemma curl_low (p: Specs G 0)(i j:Axis): curlL i j (skew _ p.val)=0:= by
    change stepValue (reach (tip j) (p.val j)) i-stepValue (reach (tip i) (p.val i)) j=0; rw [reach0 _ _ Fin.elim0,reach0 _ _ Fin.elim0]; ext1 z; simp only [stepValue,Pi.sub_apply,sub_self];rfl
lemma heat_root (p: Specs G 0)(j:Axis): orderK j (skew _ p.val)=0:= by simp [orderK,curl_low] -- inspect

def downKG(n:ℕ): (Specs G n) →ₗ[ℝ] Axis→Cover→ G.Color:= LinearMap.pi (fun i => orderK i ∘ₗ skew n ∘ₗ (evenShape n).subtype)
abbrev Okay (G:Gauge)(n:ℕ):= ↥(LinearMap.ker (downKG (G:=G) n))
lemma heat_diag (Q : TwoJet G.Color (n+1))(hQ:ClosedJet Q)(i:Axis) : diagonal (heat i Q) = fun x=> ∑ j:Axis, Maxwell.grad j (diagonal (Q j i)) x:= by funext x; rw [heat_apply]; change (∑ j:Axis, burst j (Q j i)) _= _; rw [_root_.sum_apply]; refine sum_congr rfl fun j _=> burst_diag (hQ.coeffSym j i) j _
lemma coolZ (Q:TwoJet G.Color 0)(hQ:ClosedJet Q) : Q ∈ onShell G.Color 0:= by
    refine ⟨hQ,fun b x=>sum_eq_zero (fun i _=> ?_)⟩;rw [show diagonal (Q i b)= fun _ => diagonal (Q i b) 0 from funext (fun _=>congr_arg (Q i b) (Subsingleton.elim (α:=Fin 0→E4) ..))]; simp [grad,Analysis.D]
lemma cool (Q: TwoJet G.Color (n+1))(hQ:ClosedJet Q) : Q∈onShell G.Color (n+1) ↔ ∀ j:Axis, heat j Q=0 := by
    refine ⟨fun ⟨_,h⟩ j=> ext_diag _ _ (heat_sym j Q hQ) (fun _ _=> rfl) ?_, fun hh =>⟨hQ,fun b x=> ?_⟩⟩
    · rw [heat_diag Q hQ]; exact funext (h j)
    change (fun x=> ∑ i:Axis, Maxwell.grad i (diagonal (Q i b)) x) x=0; rw [← heat_diag Q hQ,hh]; rfl
lemma top_injective (δ:E4)(p:T E4 V n)(h:Tensor.Sym p)(he:reach δ p=0): p=0:= by
    apply seedEq; intro i; apply smul_right_injective V (show (n.factorial:ℝ) ≠ 0 by positivity); dsimp only; rw [←top h δ i 0,he,jumps_zero]; simp
lemma down_condition (p:Specs G (n+1)) : p ∈ LinearMap.ker (downKG _) ↔ trot p.val ∈ onShell G.Color n:= by
    cases n with
    | zero=> exact iff_of_true (funext (heat_low p)) (coolZ _ (trot_closed p))
    | succ n=>
       rw [cool _ (trot_closed p)]
       constructor
       · intro h j; apply top_injective (tip j) _ (heat_sym _ _ (trot_closed p)); apply neg_eq_zero.mp; rw [← map_neg,← heat_K]; exact congr_fun (LinearMap.mem_ker.mp h) j
       intro h; change downKG (n+2) p=0; funext i; change orderK i (skew _ p.val)=0; rw [heat_K,h,neg_zero,map_zero]

def shelve (n:ℕ): Okay G (n+1) →ₗ[ℝ] Maxwell.Shell G n:= ((trot ∘ₗ (evenShape _).subtype) ∘ₗ (LinearMap.ker (downKG _)).subtype).codRestrict _ (fun v=> (down_condition v.val).mp v.property)
lemma prec (v:Maxwell.Shell G n): trot (gaugeJet v).val=v.val:= by
    conv_rhs => rw [← match_leg v]
    funext i j; ext1 l; change (burst i ((gaugeJet v).val j)-burst j ((gaugeJet v).val i) : T E4 G.Color n) _= _
    simp only [sub_apply,takeCurl,burst_eval,Nat.cast_smul_eq_nsmul, smul_apply,smul_sub]

def slash : Maxwell.Shell G n→ₗ[ℝ] Specs G (n+1) := (((Labels.radial G n).subtype) ∘ₗ gaugeJet).codRestrict _ (fun u i _=> (gaugeJet u).property.1 i) -- inspect
lemma slash_prop (v:Maxwell.Shell G n): slash v ∈ LinearMap.ker (downKG _) := (down_condition ..).mpr ((prec v).symm ▸ v.property)
def slip : Maxwell.Shell G n→ₗ[ℝ] Okay G (n+1) := slash.codRestrict _ slash_prop
lemma shelve_slip (v:Maxwell.Shell G n): shelve n (slip v)=v:= Subtype.ext (prec v)
lemma slash_eq (v:Maxwell.Shell G n): (slip v).val.val=(gaugeJet v).val:= rfl
end YM.PositionX.Reed
