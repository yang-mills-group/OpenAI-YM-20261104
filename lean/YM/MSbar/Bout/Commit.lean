import YM.MSbar.Bout.Depart
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bout
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Parma Portal
variable {G:Gauge}{c f:Side}{S:StepData c f}(F:Forest S.ratio)(v:S.Choices)(x:Positions (Primary c G))(w:Positions (Key F G))(l:List (Primary c G))(i:Primary c G)(p:ℕ)
variable {t B K r:ℝ}
local notation "Y"=>Positions (Primary c G)
local notation "E"=>Positions (Joint F G)
local notation "X"=>meetVar x w
local notation "L"=>l++[i]
local notation "J"=> Lis.rope i
local notation "C"=> pushChart F G v
local notation "A₀"=> arch F v (Lis.rope i)
local notation "A"=>singularity (pushChart F G v) 2
lemma brace : hands F G i = bolt (Sum.inl i):=by
    funext z; cases z with
    | inl a=> change bolt i a=_; by_cases hp:i=a <;> simp_all [bolt,Pi.single_apply]
    | inr j=> change 0=_; simp [bolt,Pi.single_apply] -- lex
lemma springP : cycleP F v (l++[i])= Yarn l.length (fun t:List Bool=> cycleP F v (takeout true t l)* Jets F v (takeout false t l++[i])):=by
    unfold cycleP; rw [yieldP]; apply stitch; intro m he; change _= _*Jets F v (takeout false m l++[i]); unfold Jets; congr 1; generalize takeout false m l = T'; induction T' with|nil=>rfl|cons a T' ih=> rw [List.cons_append,rungP,rungP,ih]
lemma narrow {σ:Type}(l:List σ)(b:Bool)(f:List Bool):takeout b f l⊆ l:=by
    induction l generalizing f with
    | nil=>cases f <;> exact List.nil_subset _
    | cons a l ih=> cases f with|nil=> exact List.nil_subset _|cons v f=> by_cases ht:v=b <;> rw [takeout]; rw [if_pos ht]; exact List.cons_subset_cons _ (ih _); rw [if_neg ht]; exact List.Subset.trans (ih _) (fun k hk => List.mem_cons_of_mem _ hk)
variable (z:Site f)
local notation "j"=>address F G
local notation "μ"=>PowerSeries.coeff
local notation "T"=>rungP (hands F G)
lemma prune (k:ℕ)(g:SpringK (Joint F G)) (v:Primary c G) (t:List (Primary c G)):μ k (rungP (hands F G) (v::t) g)=pderiv (Sum.inl v:Joint F G) (μ k (rungP (hands F G) t g)):=by rw [rungP,flux,ride,brace,dintX] -- replace
lemma edgesD (a:ℕ)(hk:a ≤ p): (PowerSeries.coeff a (Jets F v (l++[i]))).totalDegree ≤ p+2 :=by
   let x':= (-A); unfold Jets; induction l with
   | nil=> rw [List.nil_append,prune,rungP,_root_.map_neg,singularity,PowerSeries.coeff_mk]; apply pdeg; rw [totalDegree_neg]; exact (potsD ..).trans (by omega)
   | cons u w IH=> rw [List.cons_append,prune]; exact pdeg _ (IH.trans (Nat.le_succ _))
variable {m b d s N:ℕ}{a:ℝ}
noncomputable def ranged (F:Forest S.ratio)(l:List (Primary c G))(z:Site f)(D:ℕ):Prop:= ∀ i∈ l,separation z (address F G (Sum.inl i)) ≤ D
variable (h: Tokew (address F G) a s m 0 (PowerSeries.coeff p (singularity (pushChart F G v) 2)) B) (he:ranged F (l++[i]) z N)
include h
lemma conspire (ha:0≤a) : Vault (address F G) {j (Sum.inl i)} a s m 0 (PowerSeries.coeff p (Jets F v [i])) B:=by
   unfold Jets; rw [prune,rungP,_root_.map_neg]; rw [show pderiv _ _= _ from Derivation.map_neg ..,← neg_one_smul ℝ]; exact Quote.widen (Quote.mulR (h.2 _) (-1)) (by simp) le_rfl
include he
lemma behalf (ha:0≤a)(hu:d+l.length≤ m) :Vault (address F G) {z} a s d 0 (PowerSeries.coeff p (Jets F v (l++[i]))) (liftW a s N*B):=by
    induction l generalizing d with
    | nil=> rw [List.nil_append]; refine Quote.widen (Bout.tau ha (conspire F v i p h ha)) (mul_le_mul_of_nonneg_right (w_more (he i (by simp)) ha _) h.1) (by simpa using hu)
    | cons i' t IH=> have hh :ranged F (t++[i]) z N:=fun k hk=>he _ (List.mem_cons_of_mem i' hk); rw [List.cons_append,Jets,prune]; refine orbital (show ({z}:Finset _) ⊆ insert (address F G (Sum.inl i')) {z} from Finset.subset_insert ..) ha (Quote.spice (IH hh (d:=d+1) (by rw [List.length_cons] at hu; omega)) _)
end YM.MSbar.Bout
