import YM.MSbar.Duel.Oven
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Duel
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Further.GaussianScalar
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {σ ι τ:Type}[Fintype σ][Fintype τ][Fintype ι][DecidableEq ι][DecidableEq σ][DecidableEq τ]
variable {m p:ℕ}
local notation "µ"=> PowerSeries.coeff
local notation "P"=> Pot σ
local notation "Q"=> Pot ι
local notation "V"=> View σ
local notation "W"=>View ι
local notation "R"=> SpringK σ
-- concrete directional polynomial partial
local notation "H"=>SpringK σ
local notation "G"=>SpringK ι
local notation "B"=>View τ
variable (A:Matrix σ ι ℝ)(C': Matrix σ τ ℝ)(D:Matrix τ τ ℝ) (h:D.PosDef)
local notation "L"=> C'*D*C'.transpose
set_option quotPrecheck false
local notation "ν"=> PowerSeries.map (rail A).toRingHom
variable (β γ:SpringK σ)
local notation "S"=> Spring β
local notation "fA"=> ν (confect L β)
variable (b:ι→ View σ)(M:ι→ View τ)(K: Pot ι)(G₀:ι → Pot σ)
variable (hM:Mold A C' D b M K G₀)
local notation "c"=>PowerSeries.C
variable (hβ:Kind β)
include h hM hβ
lemma hence (l:List ι) : Lap p (ν (growP β (readScore b G₀ β l) L (p+1))) (port K fA l) :=by
    let f:=fA; let v:= readScore b G₀ β l; let X:=ν (growP β v L (p+1)); let g:= port K fA l
    have hp(j:ℕ)(ht:j≤p): µ j (X*Spring fA)= µ j (g*Spring fA):=by
       have hy : X*Spring fA=ν (growP β v L (p+1) * Spring (confect L β)):=by rw [sunshine, _root_.map_mul]; -- x def
       have hz:= orbit A C' D h β b M K G₀ hM hβ l
       rw [hy,show g*Spring fA= _ from hz.symm,PowerSeries.coeff_map,PowerSeries.coeff_map,nick]; apply congr_arg; apply MvPolynomial.funext; intro x; exact (aromaEval C' x h β _ hβ (by omega : j < p+1)).trans ((show Summer D C' x _ from seen C' x h _) |> Eq.symm)
    have ht: Kind fA:=by unfold Kind; rw [PowerSeries.coeff_map,sugar L hβ, _root_.map_zero]
    let g':=Spring fA; obtain ⟨V',hV⟩:=solitary (f:=fA) ht; have hh : Lap p (X*g'* ((V'⁻¹:_) : G)) (g*g'* ((V'⁻¹:_) : G)):= Lap.rises hp (fun _ _=> rfl); simp_rw [show g'=↑V' from hV.symm, mul_assoc,V'.mul_inv,mul_one] at hh; exact hh
omit hM hβ h
-- Leib product formula for abstract output ratios. Span list stamps.Left.Head.Coilon.
variable (i:σ)(l:List σ)
noncomputable def rungP (b:ι→View σ) : List ι→H→H
| [],v=>v
| i::l,v=> flux (b i) (rungP b l v)
lemma billQ (f:SpringK σ)(l:List σ)(i:ℕ)(x:View σ): MvPolynomial.eval x (µ i (rungP (fun i:σ=> Uniform.bolt i) l f))= buoy (fun y=>eval y (µ i f)) x l:=by
     let p(A:H)(x:View σ):= MvPolynomial.eval x (µ i A); induction l generalizing x with
     | nil=>rfl
     | cons v l ih=> let g:=rungP (fun i:σ=> Uniform.bolt i) l f; let L':= p g; have he: L'= roc (fun y=> MvPolynomial.eval y (µ i f)) (l.map (@Uniform.bolt σ)):=funext fun z=> ih z
                     rw [rungP,flux,ride,← dimY, show buoy _ _ _=fderiv ℝ (roc (fun y=> MvPolynomial.eval y (µ i f)) _) x _ from rfl, ←he] -- m transparency
lemma yieldP (b:ι→ View σ)(F:ι→ SpringK σ)(l:List ι)(i:ι): batt b F (l++[i])=Yarn l.length (fun t:List Bool=> batt b F (takeout true t l)* rungP b (takeout false t l) (F i)):=by
    induction l with
    | nil=> have he : flux (b i) (1:R)=0:=by have he:= chip (b i) 1 1; rw [one_mul,mul_one,one_mul] at he; exact add_left_cancel (he.symm.trans (add_zero _).symm)
            rw [List.nil_append,batt,batt,he,zero_add,mul_one,List.length_nil,twillz,takeout,takeout,batt,rungP,one_mul]
    | cons j l ih=>
       let v:=F j; let f':=batt b F; let g(k):= f' (takeout true k l); let a(k):=rungP b (takeout false k l) (F i); let H₀(k) := g k*a k
       let m:=flux (b j)
       have he: Finset.sum univ (fun z':Bool=> Yarn l.length (fun k:List Bool=> f' (takeout true (z'::k) (j::l))* rungP b (takeout false (z'::k) (j::l)) (F i))) =Yarn l.length (fun k=> f' (j::(takeout true k l))* a k +g k *m (a k)):=by
           rw [Fintype.sum_bool,←pockets]; exact stitch _ fun k _=> rfl -- order.B
       let X:=AddMonoidHom.mulLeft  v -- inspect
       rw [List.cons_append,batt,ih,List.length_cons,twilled]; rw [he]
       change m (Yarn l.length (fun k=>g k*a k))+ v*Yarn l.length (fun k=>g k*a k)=_; rw [show m _=_ from (Whisk.spun m.toAddMonoidHom l.length (fun k=>g k*a k)), show v*_= _ from Whisk.spun X l.length H₀,← Whisk.pockets]; refine Whisk.stitch _ fun k _=> ?_; change flux (b j) (g k * a k)+v*(g k*a k)=(m (g k)+v*g k)*a k+ g k*m (a k); rw [chip]; unfold m; ring
lemma vapor (F:SpringK σ)(z:Pot σ)(b:View σ): flux b (PowerSeries.C z)= PowerSeries.C (dint b z):=by apply PowerSeries.ext; intro n; rw [flux,ride]; by_cases he:n=0; subst n; simp; simp [PowerSeries.coeff_C_of_ne_zero he]
lemma ovens (i:σ)(t:List σ)(f:R)(k:Pot σ): port k f (t++[i])= Yarn t.length (fun l:List Bool=> port k f (takeout true l t) * rungP (fun z:σ=> Uniform.bolt z) ((takeout false l t)++[i]) (f-PowerSeries.C k)):=by
    unfold port; rw [yieldP]; refine stitch _ fun b hb=> ?_; congr 1; suffices h:∀ l:List σ,rungP (fun z:σ=> Uniform.bolt z) l (-PowerSeries.C (dint (bolt i) k)+flux (bolt i) f)=rungP (fun z:σ=> Uniform.bolt z) (l++[i]) (f-PowerSeries.C k) from h _
    intro l; induction l with|nil=> rw [List.nil_append,rungP,rungP,rungP,_root_.map_sub,vapor f k]; ring|cons a l ih=> rw [List.cons_append,rungP,rungP,ih]
end YM.MSbar.Duel
