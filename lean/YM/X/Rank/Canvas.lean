import YM.X.Rank.Palette
/-!
Global free diagram polynomial space combining all flavors and spacetime arguments.
Uses no self edges at any location. No actual coincident-field products.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PositionX.Rank
open Function Set Maxwell Wick Maxwell.Free Next.Rank.Normal MvPolynomial
open scoped BigOperators Classical
variable {G : Gauge} {j l : ℕ} {p : Gauge.Simple G}

abbrev Stroke := E4 × Style
abbrev Fiber (G : Gauge) := Stroke × G.ColorIndex
abbrev Canvas (G : Gauge) := poly (Fiber G)
abbrev pin (x : E4) (k : Key G) : Fiber G := ((x,k.1),k.2)

abbrev scov (c : G.ColorIndex) (p q : Stroke) : ℝ := if p.1=q.1 then 0 else fare c (ax p.2.1 p.2.2) (ax q.2.1 q.2.2) (p.1-q.1)
def weft (c : G.ColorIndex) : Next.Rank.Normal.Symmetric (Fiber G) where
  cov i j := if i.2=j.2 then (scov c i.1 j.1:ℂ) else 0
  symm := by
    rintro ⟨⟨x,p⟩,i⟩ ⟨⟨y,q⟩,j⟩; dsimp
    by_cases h : i=j
    · by_cases hz:x=y
      · simp [h, scov, hz]
      simp only [h,scov,hz,Ne.symm hz, ↓reduceIte]
      congr 1; exact K_symmetric _ _ hz
    simp [h,Ne.symm h]

def pluck (x : E4) : Poly G →ₐ[ℂ] Canvas G := rename (pin x)
def prim (x : E4) : WickPol G →ₐ[ℂ] Canvas G := (pluck x).comp (paint G)
def E (c : G.ColorIndex) : Canvas G →ₗ[ℂ] ℂ := Next.Rank.Normal.blend (weft c) 0

section reading
variable {n : ℕ} {x : Points n}
private lemma reads_zero {A B : Type*}(f : A → B →₀ ℂ) : reads f 0=0 := by
  funext x; unfold reads; simp
private lemma probe_sum (p : Probe G j) : p=∑ i:Fin (legDim G j), p (Maxwell.frame G j i) • (Maxwell.frame G j).coord i := by
  apply LinearMap.ext; intro v; rw [LinearMap.sum_apply]; conv_lhs => rw [← (Maxwell.frame G j).sum_repr v]
  simp only [LinearMap.smul_apply, _root_.map_sum, map_smul,smul_eq_mul]; exact Finset.sum_congr rfl fun i _=> mul_comm ..
private lemma per (c : G.ColorIndex)(hx : x∈conf n) :
    scope (perSlot (fun _ : Fin n=>nib (G:=G))) (frameX (G:=G) hx) = scope (fun a:Fin n × Key G => Finsupp.single (pin (x a.1) a.2) 1) (weft c) := by
  let F (p : Fin n × Slot G)(q) := (frameX hx).cov p q; apply Next.Rank.Normal.Symmetric.ext; funext a b; rcases a with ⟨i,a⟩; rcases b with ⟨k,b⟩
  rw [match_name (fun v:Fin n× Key G=>pin (x v.1) v.2)]
  unfold scope treats; simp only [perSlot,Finsupp.linearCombination_mapDomain,nib,map_sum,Finsupp.linearCombination_single,Finset.sum_apply,comp_apply,Pi.smul_apply,smul_eq_mul]
  by_cases h:i=k
  · subst i; simp [frameX,weft,scov,pin]
  have he:x i ≠ x k := (show Injective x.ofLp from hx).ne h
  let z:=x i - x k
  have hz:z≠0:= sub_ne_zero.mpr he
  let L:= pairing (G:=G) (show z∈away from hz) (j:=a.1.1) (l:=b.1.1)
  have ht : L (ink a) (ink b)=(if a.2=b.2 then 1 else 0)*fare c (ax a.1.1 a.1.2) (ax b.1.1 b.1.2) z := any_ink c _ _ _ _ hz
  simp only [weft, scov, pin, he, ↓reduceIte, frameX,h,entry]
  rw [show (if a.2=b.2 then (_ : ℂ) else 0)=↑(L (ink a) (ink b)) from ?_]
  swap
  · rw [ht]; split_ifs <;> simp <;> rfl
  conv_rhs=> rw [probe_sum (ink a),probe_sum (ink b)]
  simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,Complex.ofReal_sum,Complex.ofReal_mul]; rfl

lemma wick_pluck (c : G.ColorIndex)(hx : x∈conf n)(p : Fin n→Poly G) :
    moment G x (fun i=> send G (p i))= E c (∏ i, pluck (x i) (p i)) := by
  let M := fun _:Fin n=>nib (G:=G)
  let f (a: Fin n × Key G):=pin (x a.1) a.2
  let A := (∏ i,post i (p i)); rw [Wick_reads hx]
  have hF : ∏ i, pluck (x i) (p i)=rename f A:= by unfold A; rw [_root_.map_prod]; refine Finset.prod_congr rfl fun i _=>?_ ; apply DFunLike.congr_fun (g:=(rename f).comp (post i)); ext1 u; rw [AlgHom.comp_apply,post_X, rename_X]; exact rename_X ..
  have hP : ∏ i, post i (send G (p i))= Next.Rank.Normal.exchange (perSlot M) A := by unfold A; rw [map_prod]; exact Finset.prod_congr rfl fun i _=> (Next.Rank.Normal.posts M i (p i)).symm
  change Next.Rank.Normal.blend (frameX _) 0 (∏ i, post i (send G (p i)))= _
  rw [hP,wets,hF,E,labelled,wets,reads_zero,reads_zero]; exact DFunLike.congr_fun (congr_arg (fun v=>Next.Rank.Normal.blend v 0) (per c hx)) _
lemma wick_prim (c : G.ColorIndex)(hx : x∈conf n)(p:Fin n→ WickPol G) :
    moment G x p= E c (∏ i, prim (x i) (p i)) := by
  convert! wick_pluck c hx (fun i=>paint G (p i)) using 1; simp_rw [sendPaint]
end reading
end YM.PositionX.Rank
