import YM.FVA2.Parameters
import YM.FVA2.Shipment
/-!
# Finite price books for the conditional series including inherited unmarked terms

Here extending Fork.* on a fixed foreground analytic Germ (we'll choose inherited unmarked
 **quadratic plus this step's full classical block penalty**). Inherited interactions, formal
 coupled β/penalty corrections are tickets *relative to that engine* (explicit identities).
 Every Ticket entry, arbitrary polynomial in rescaled log links, fast and yet unintegrated
 slow, realizes through Fk.read exactly, then put back external powers/coupling series. Same
 denominator for any set of incoming marks. Estimate at fixed geometry requires no sector/Ray
 comparison to actual analytic `Fork.expect`.

For an all-order recursion it is crucial to be able to do this identification in a way **not
 imposing** that the already re-expanded unmarked or source system is even analytic in unscaled
 links after a coupling substitution. The `catalog` proof below works even when rank >> power.
 No uniform polynomial cost claim on that inventory in THIS file. Use the free Wilson predictions
 (not Fk evaluation of an interacting input model unless choosing it to be the specified one).
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.RayScatter.Harvest
open Filter Topology Function PowerSeries Finset MeasureTheory Lattice
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Splice
open FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.OpenSlots FormalOPE.RG10.Sync
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Precision
open GaussianScore RGComparison.Core16 RGComparison.Core16.Therm RGComparison.Core16.Lumen
open scoped Topology ContDiff Classical BigOperators

section catalog
variable {E R:Type} [NormedAddCommGroup E][NormedSpace ℝ E]
variable (E)
structure Cart where
    value: Permit E
    degree: ℕ
    price (x:E)(t:ℝ): value.val (t•x)=t^degree*value.val x
variable {E}
namespace Cart
instance : Mul (Cart E) where
    mul a b:=⟨ a.value*b.value,a.degree+b.degree,fun v t=> by change a.value.val _*b.value.val _=t^ _*(_*_); rw [a.price,b.price,pow_add]; ring ⟩
@[simp] lemma value_mul (a b:Cart E) : (a*b).value=a.value*b.value:=rfl
def worthL (L:List (Cart E)): Permit E:= ( L.map Cart.value ).sum
@[simp] lemma total_nil : worthL ( []:List (Cart E) )=0:=rfl
@[simp] lemma total_join (a b:List (Cart E)): worthL (a++b)=worthL a + worthL b:= by simp [worthL]
@[simp] lemma cons (x:Cart E)(b:List (Cart E)): worthL (x::b)= x.value + worthL b:= by unfold worthL; rw [ List.map_cons,List.sum_cons]
lemma one_total (x:Cart E): worthL [x]=x.value:= by simp
lemma found (u:Permit E): ∃ b:List (Cart E), worthL b=u:= by
    have hx (w:E→ℝ)(h:w∈papers E): ∃ b:List (Cart E), ( worthL b ).val=w:= by
       apply Papers.induction (P:=fun p:E→ℝ=>∃ b:List (Cart E),( worthL b ).val=p) ?_ ?_ ?_ ?_ h
       · intro ℓ; let a:Cart E:= ⟨ ⟨ℓ,Papers.linear ℓ⟩,1,fun x t=> by change ℓ (t•x)= t^1*( ℓ x ); rw [ map_smul,pow_one ]; rfl⟩; exact ⟨ [a], congr_arg Subtype.val (one_total a)⟩
       · intro x; let a:Cart E:=⟨ ⟨fun _=> x,Papers.fixed x⟩,0,fun u t=>by change x= t^0*x; rw [pow_zero,one_mul]⟩; exact ⟨[a],congr_arg Subtype.val (one_total a)⟩
       · rintro x y _ _ ⟨a,rfl⟩ ⟨b,rfl⟩; exact ⟨ a++b,congr_arg Subtype.val (total_join a b) ⟩
       rintro x y _ _ ⟨a,rfl⟩ ⟨b,rfl⟩; exact ⟨ _,congr_arg Subtype.val (total_mul a b) ⟩
    obtain ⟨b,h⟩:=hx u.val u.property; exact ⟨ b,Subtype.ext h⟩
where
 total_mul (a b:List (Cart E)) : worthL (a.flatMap fun x=>b.map (x*·))= worthL a * worthL b:= by 
    induction a with
    | nil=> simp
    | cons i a H=>
      have he(i:Cart E)(t:List (Cart E)): worthL (t.map (i*·))= i.value*worthL t:= by induction t <;> simp_all [mul_add];
      simp [H,he,add_mul] -- long indentation?

def catalog (u:Permit E):List (Cart E):= (found u).choose
lemma totals (u:Permit E): u=worthL (catalog u):=(found u).choose_spec.symm
variable [FiniteDimensional ℝ E]
lemma mon (u:Cart E) : Stack.rise u.value.val = X ^ u.degree * C u.value := by
   let L:E→ℝ:=u.value.val
   let d:=u.degree; have he(v:E)(i:ℕ):jet L i v= if i=d then L v else 0:= by rw [ homogeneous_derivative L v i ( ( Boson.paper_hot u.value|>.contDiffAt).of_le le_top ), show (fun t:ℝ=> L ( t • v ))=(fun t:ℝ=> t^d * L v ) from funext ( fun i=>u.price v i ), iteratedDeriv_mul_const_field, iteratedDeriv_fun_pow_zero ]; split <;> rename_i h; (subst i; simp [Nat.factorial_ne_zero]); simp
   apply PowerSeries.ext; intro i; apply Subtype.ext; funext x
   rw [Stack.rise, coeff_mk]; by_cases h:i=d; · subst i; rw [ mul_comm, coeff_C_mul_X_pow ]; change jet L d x=_; rw [if_pos (show d=u.degree from rfl)]; exact Eq.trans (he x d) (if_pos rfl) -- d vs u.degree def nor simp
   rw [mul_comm, coeff_C_mul_X_pow ]; split
   · exact False.elim (h (by assumption))
   exact (he x i).trans (if_neg h)
end Cart

variable {R S:Type}[CommRing R][CommRing S]
def omitTail (t:PowerSeries R) (n:ℕ):= ∑ i∈Finset.range (n+1), X^i * C (coeff i t)
lemma top_omitted (t:PowerSeries R)(n:ℕ): Through n t (omitTail t n):= by
    intro i hi; unfold omitTail; rw [_root_.map_sum, Finset.sum_eq_single i,mul_comm,PowerSeries.coeff_C_mul_X_pow, if_pos rfl]; intro j hj H; rw [mul_comm,PowerSeries.coeff_C_mul_X_pow, if_neg (Ne.symm H)];  exact fun h=> False.elim (h (Finset.mem_range.mpr (by omega)))
end catalog
variable {G:Gauge}{S:Side}{ι k T A D L I K U0:Type}[Fintype ι][Fintype k][Fintype U0]

-- common Stuff type for this foreground identification.All analytic coefficient labels read
-- using SAME map of fast links and retention points. All zero padding allowed.Fork phase fixed.
local notation "Fκ" => Fk.Panel G ι
local notation "U" => Fk.Panel G U0
local notation "Ξκ" => Fκ × U
local notation "J" => Cart ( Ξκ )
def pen (y:Fk.Panel G U0) : Stuff G ι (ι⊕U0):= Sum.elim Sum.inl (Sum.inr ∘ y)
def decode (u : J)(x: (ι ⊕ U0)→ G.Color):= u.value.val (fun i=> Inherit.down (fun p:ι=> RGComparison.Core16.Lumen.launch (x (Sum.inl p))) i,x ∘ Sum.inr)
omit [Fintype k] in
lemma fitted (u:J)(y:U): ( decode u ∘ Fk.scene (pen y) )=ᶠ[𝓝 0] u.value.val ∘ recover y:= by
    have hv : Tendsto (Fk.spread (G:=G) (ι:=ι)) (𝓝 0) (𝓝 1):= by
        apply tendsto_pi_nhds.mpr; intro i; simpa [Fk.spread] using! ((show Continuous fun x:Fκ => G.lieExp (x i) from G.lieExp_cont.comp (continuous_apply i)).tendsto 0)
    have hF : ∀ᶠ x:Fκ in 𝓝 0,∀ i,launch (G.curvature (Fk.spread x i))=Fk.spread x i:= hv.eventually (Filter.eventually_all.mpr (fun i=> ((continuous_apply i).tendsto _).eventually leaving))
    filter_upwards [ (continuous_snd.tendsto (0:Fk.Door G ι)).eventually ( hF.and Inherit.down_left ) ] with p hp
    unfold decode Function.comp; apply congr_arg u.value.val; refine Prod.ext ?_ rfl; rw [ show (fun i:ι=>launch ( Fk.scene ( pen y ) p (Sum.inl i)))=Fk.spread p.2 from funext (fun i=> hp.1 i) ]; exact hp.2

variable {X:Shelf G A D}(P:Planet X S ι k T)(Z:ChartRatio G)(hZ:LocalRatio Z)
variable {b:ℝ}{p:Fk.Panel G ι × Fk.Panel G U0→ℝ}
    (h:ContDiffAt ℝ ω p 0)(Q:Quadratic (Fk.Panel G ι × Fk.Panel G U0))(hy:∀ v,Q.flourish v=2*jet p 2 v)
    (hp:(Quadratic.core Q).RespectsPrice)(y:Fk.Panel G U0)
local notation "μ"=> tangent G ι
local notation "W0"=> (Fork.interaction Z p)
local notation "xη"=>Q.uptake μ hp
local notation "ν"=>Stack.read y
local notation "Sκ"=> Cart ( Fκ × U )
-- NOTICE `X` variable already used for Shelf. use qualified.
def localPay (P:Planet X S ι k T)(Z:ChartRatio G)(y:Fk.Panel G U0) (q:Permit (Fκ × U)) (j:ℕ) : ℝ:= ((Cart.catalog q).map (fun v=> Fk.read P Z ( pen y ) ( decode v ) v.degree j)).sum -- j: Nat
local notation "Tκ"=> basePower Q hp y μ b * Stack.overhead Z ι
local notation "lk"=> localPay P Z y
variable (hc:Fk.rise P =ᶠ[𝓝 0] charge p b y)

def collect (Z:ChartRatio G){p:Fk.Panel G ι × Fk.Panel G U0→ℝ}(Q:Quadratic (Fk.Panel G ι × Fk.Panel G U0))(hp:(Quadratic.core Q).RespectsPrice)(y:Fk.Panel G U0): Ticket ( Fκ × U )→+ PowerSeries ℝ where
   toFun r:= Stack.read y ( Q.fit μ hp r (Fork.interaction Z p) )
   map_zero' := by change Stack.read y (Q.fit (tangent G ι) hp (0:Ticket _) (Fork.interaction Z p))=_; rw [ Quadratic.fit,mul_zero,map_zero,zero_mul,map_zero ]
   map_add' a b:= by unfold Quadratic.fit; rw [mul_add,map_add,add_mul,map_add]
lemma current_X (r:Ticket ( Fκ × U ))(i:ℕ): collect Z (p:=p) Q hp y ( PowerSeries.X^i * r )= PowerSeries.X^i*( collect Z (p:=p) Q hp y r):= by
    change ν ( Q.fit μ hp (PowerSeries.X^i * r) W0 )= _; unfold Quadratic.fit; rw [mul_left_comm W0 ( PowerSeries.X^i ), show (xη) (_ )=PowerSeries.X^i * _ from Shipment.transferX _ _,mul_assoc,map_mul,map_pow, show (ν) PowerSeries.X=PowerSeries.X from map_X _ ]; rfl
include h hy hZ hc
lemma collector (u:Sκ) : collect Z (p:=p) Q hp y ( C u.value ) = PowerSeries.mk (Fk.read P Z (pen y) (decode u) u.degree):= by
     rw [ Fork.perch P Z hZ h Q hy hp y (pen y) hc u.value.val (fitted u y) ( Boson.paper_hot u.value|>.contDiffAt ) u.degree, Cart.mon ]; change collect Z Q hp y (p:=p) ( C u.value ) = Stack.drop u.degree (collect Z Q hp y (p:=p) (PowerSeries.X^ u.degree * C u.value)); rw [ current_X, Stack.drop_mul ] -- syntax ...
lemma hunt (u:Permit (Fκ × U))(j:ℕ): coeff j (collect Z (p:=p) Q hp y ( C u ))= localPay P Z y u j:= by
   nth_rw 1 [ Cart.totals u ]; let l:= Cart.catalog u; change _=( List.map _ l ).sum; unfold Cart.worthL; simp_rw [map_list_sum, List.map_map ]; congr 1
   apply List.map_congr_left; intro a ha; unfold Function.comp; rw [ collector P Z hZ h Q hy hp y hc,coeff_mk ]
-- actual evaluators

def page (P:Planet X S ι k T)(Z:ChartRatio G)(y:Fk.Panel G U0) (r:Ticket ( Fκ × U )) : PowerSeries ℝ:= PowerSeries.mk fun j=> ∑ i∈Finset.range (j+1), localPay P Z y (coeff i r) (j-i)

lemma pages (r:Ticket ( Fκ × U )): page P Z y r= collect Z (p:=p) Q hp y r:= by
    apply PowerSeries.ext; intro j
    have hh: Through j (collect Z (p:=p) Q hp y r) (collect Z (p:=p) Q hp y (omitTail r j)):= by
       let W : Ticket ( Ξκ ):= W0; let T:=omitTail r j;
       have hy : Through j (Q.fit μ hp r W) ( Q.fit μ hp T W):= Through.mul ( keepsThrough _ ( (Through.refl W).mul (top_omitted r j) ) ) (Through.refl _) -- arguments 
       intro k hk; change coeff k (ν (Q.fit μ hp r W))=_; rw [Stack.reading_term,hy k hk]; exact (Stack.reading_term ( Q.fit μ hp T W) k y).symm
       -- transport through
    rw [hh j le_rfl, page,coeff_mk,omitTail, map_sum,map_sum]; symm; apply Finset.sum_congr rfl; intro i hi; rw [ current_X,coeff_X_pow_mul', if_pos ( by rw [Finset.mem_range] at hi; omega ) ]; exact hunt P Z hZ h Q hy hp y hc _ _


-- restore full conditioned cost from all-ticket interaction. Include preferably the full
-- lower action name in prescription; relative interactions declared, no mismatched theta estimate
variable (W: Ticket (Fk.Panel G ι × Fk.Panel G U0))(hw: incline W)(r:Ticket (Fk.Panel G ι × Fk.Panel G U0))
abbrev shift (v:Ticket (Fk.Panel G ι × Fk.Panel G U0)) : Ticket (Fκ × U) := Return (Fork.interaction Z p)* v
local notation "H'"=> ( Fork.inclineI (p:=p) Z hZ )
local notation:max "φ" led:arg=> (page P Z y (shift Z led (p:=p)))

include hp
lemma income_all (r:Ticket (Fκ × U)) : PowerSeries.mk (Fk.birth P Z) * φ r=C Tκ * ν (xη r):= by
    rw [pages P Z hZ h Q hy hp y hc, Fork.uniform_nil P Z hZ h Q hy hp y hc]; rw [mul_assoc]; congr 1; unfold collect; change ν _ * ν _=_; rw [← map_mul,Quadratic.fit_eq Q μ hp (shift Z r (p:=p)) W0 H',shift,←mul_assoc (Fork.interaction _ _), spend_it H',one_mul]
include hw
lemma page_up : constantCoeff ( φ W )=1:= by
    rw [pages P Z hZ h Q hy hp y hc]; change constantCoeff ((ν) (_))=_; rw [← coeff_zero_eq_constantCoeff_apply, Stack.reading_term, coeff_zero_eq_constantCoeff_apply, show constantCoeff (Q.fit μ hp (shift Z W (p:=p)) W0)=1 from ?_ ]; rfl
    unfold Quadratic.fit shift; rw [map_mul, ( show constantCoeff ( xη ( W0 * (Return W0* W) ) )=1 from Quadratic.upright Q μ hp (pool H' ( pool (investment H') hw )) ),( show constantCoeff ( Return ( xη W0 ) )=1 from investment (Quadratic.upright Q μ hp H') ),mul_one]
lemma full_order : ν ( Q.fit μ hp r W )= φ (W*r) * (φ W)⁻¹:= by
    have he (u:Ticket (Fκ × U)):= income_all P Z hZ h Q hy hp y hc u
    have hv: constantCoeff (mk (Fk.birth P Z)) ≠0 := by rw [constantCoeff_mk]; exact ( Fork.positive P Z hZ h Q hy hp y hc ).ne'
    apply (eq_mul_inv_iff_mul_eq
      (show constantCoeff (φ W) ≠0 from (page_up P Z hZ h Q hy hp y hc W hw).trans_ne one_ne_zero)).mpr
    let I:= mk (Fk.birth P Z); have hz : IsUnit I := (PowerSeries.isUnit_iff_constantCoeff).mpr (isUnit_iff_ne_zero.mpr hv); apply hz.mul_left_cancel; rw [ mul_comm _ (φ W), ← mul_assoc,show I*φ W=_ from he W, mul_assoc, ← map_mul, Quadratic.fit_eq Q μ hp _ W hw , show I * φ (W*r)=_ from he _ ]

end YM.FVA2.RayScatter.Harvest
