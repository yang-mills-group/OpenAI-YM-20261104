import YM.SignedWilsonExpansion.Belle.Path
/-! # Compact-view budget. For use also on irregular sets or star-containing columns. projections. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.SignedWilsonExpansion.Belle.Path
open FVA2 FVA2.Scale FVA2.Dframe Dancer Dancer.Drawing Dancer.SeatsW
open Function Filter Set Asymptotics MeasureTheory XSpace XSpace.Structure1 Normalize
open MS MS.Menus MS.Puff MS.High MS.Native MS.Land MS.Fleet Maxwell Maxwell.Free Maxwell.Wick
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} {a b m n d:ℕ}{ι X E:Type*}{L:Filter ι}{t ν:ℝ}
section budgets
-- Trivial on empty. alternate characterization via comap.F
variable [SeminormedAddCommGroup E]
variable {x y z:ι→ X→ E}{U V:Set X}{p q:ι→ℝ}
def Serves (L:Filter ι)(x y:ι→ X→ E) (U:Set X)(p:ι→ℝ): Prop := ∀ ε:ℝ,0<ε→ ∀ᶠ i in L,∀ u∈U, ‖x i u-y i u‖ ≤ ε*‖p i‖
abbrev diners (L:Filter ι)(U:Set X): Filter (ι×X):= L ×ˢ Filter.principal U
abbrev buys (x:ι→X→E)(y:ι×X):= x y.1 y.2
lemma diners_clause {H:ι×X→ Prop}: (∀ᶠ i in diners L U,H i)↔ ∀ᶠ i in L,∀ u∈ U, H ( i,u ):=by
    rw [diners,eventually_prod_principal_iff]; -- names
lemma Serves.read (s:Serves L x y U p) {u:ι→X}(h:∀ᶠ i in L,u i∈U): (fun i=>x i (u i) -y i (u i) )=o[L] p:= IsLittleO.of_bound (fun ε he=> Eventually.mp h ((s ε he).mono (fun i hi ht=> hi (u i) ht))) -- order s implicit ε?
lemma banquet : Serves L x y U p ↔ buys (x-y)=o[diners L U] (p∘Prod.fst) := by
    rw [isLittleO_iff]; exact forall_congr' fun _=>imp_congr_right fun _=> by rw [diners_clause]; rfl -- epsilon implicit
lemma plot_le : Tendsto Prod.fst (diners L U) L:= tendsto_fst
lemma plot_in : ∀ᶠ i:ι×X in diners L U,i.2∈U:= diners_clause.mpr (Eventually.of_forall fun i u h=> h)
lemma Serves.trans (s:Serves L x y U p)(w:Serves L y z U p): Serves L x z U p:= banquet.mpr (((banquet.mp s).add (banquet.mp w)).congr_left fun i=> by simp [buys]) -- abel
lemma Serves.left (s:Serves L x y U p)(hq: V⊆U): Serves L x y V p:= fun ε he=> (s ε he).mono fun i hi u h=> hi u ( hq h )
lemma Serves.symm (s:Serves L x y U p): Serves L y x U p:= fun ε he=> ( s ε he ).mono (fun i hi u h=> (norm_sub_rev _ _).trans_le (hi u h))
lemma Serves.up (s:Serves L x y U p)(w:p=O[L] q): Serves L x y U q:= banquet.mpr ((banquet.mp s).trans_isBigO (w.comp_tendsto plot_le))
lemma Serves.fix (s:Serves L x y U p){x' y':ι→ X→ E}(h:∀ᶠ i in L,EqOn (x i) (x' i) U)(k:∀ᶠ i in L,EqOn (y i) (y' i) U): Serves L x' y' U p:= fun ε he=> by filter_upwards [h,k,s ε he] with i hi hv hs u hu; rw [← hi hu,← hv hu]; exact hs u hu
end budgets
-- any horizon renderer
variable {U:Set (Points n)}{p q τ:ι→ℝ}
def Roi (U:Set (Points n)):Prop:= IsCompact U∧ U ⊆ conf n
lemma Testi (φ:Test n): Roi (tsupport φ):= ⟨φ.hasCompactSupport,φ.tsupport_subset⟩
-- from occupied banquet (supports suffice). Clock authority.
lemma paidProfile (φ:Test n){x y:ι→ Points n→ℂ}(s: Serves L x y (tsupport φ) p) (hx:∀ᶠ i in L, ContinuousOn (x i) (conf n))(hy:∀ᶠ i in L, ContinuousOn ( y i ) ( conf n )) : (fun i=> φ.applyTo ( x i ) - φ.applyTo ( y i ))=o[L] p :=by
    refine IsLittleO.of_bound fun c hc=>?_ ; let C:= ∫ i:Points n,‖φ i‖; have pC:0≤C:= integral_nonneg (fun _=>norm_nonneg _)
    filter_upwards [ s (c/(C+1)) (by positivity),hx,hy ] with i hi hx hy; unfold Test.applyTo; rw [←integral_sub (φ.smearing hx) (φ.smearing hy)]
    let k:=c/(C+1)*‖p i‖; have he(u:Points n): ‖φ u*x i u-φ u*y i u‖≤‖φ u‖*k := by
       by_cases hu:u∈tsupport φ; · rw [←mul_sub,norm_mul]; exact mul_le_mul_of_nonneg_left (hi u hu) ( norm_nonneg _ )
       simp [image_eq_zero_of_notMem_tsupport hu]
    have hw:C*k≤ (C+1)*k:= mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by unfold k; positivity); refine ( norm_integral_le_of_norm_le ((φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).norm.mul_const k) (Eventually.of_forall he) ).trans (?_); rw[integral_mul_const]; exact hw.trans_eq (by unfold k; field)
variable (W:Initialize G){V: Normalize.Store G}(K: Rose.Pick V){Y:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {S:Prescription (Press.portDeck G)}(M:Speed.Quoted W K Y S)(s:G.Simple)
local notation "D"=>FVA2.Scale.Measure.start W K d
include s M
lemma cost (h:Roi U)(k:ℕ)(x:Tags G d n): buys (fun _:ι=> (fun p=> Jury.fxt D p k x))=O[diners L U] (1:ι×Points n→ℝ):=by
    obtain ⟨C,v⟩:= (h.1.image_of_continuousOn ((smooth_c W K M s x k).norm.mono h.2)).bddAbove; exact IsBigO.of_bound C ( plot_in.mono fun i h=> (v (mem_image_of_mem _ h)).trans_eq (by simp) )
lemma price (h:Roi U)(k:ℕ)(x:Tags G d n)(f:τ=O[L] (1:ι→ℝ)): buys (fun i y=> mote D k y (τ i) x)=O[diners L U] (1:ι×Points n→ℝ):=by
    let hp:= @plot_le ι (Points n) L U; have hx:(fun v:ι×Points n=>( (τ v.1):ℂ))=O[diners L U](1:ι×Points n→ℝ):= (IsBigO.of_norm_left (by simpa only [Complex.norm_real, Function.comp_apply, show (1:ι→ℝ) ∘ (Prod.fst:ι×Points n→ι)=(1:ι×Points n→ℝ) from rfl ] using (f.comp_tendsto hp).norm_left)) -- cast syntax check
    change (fun i=> ∑ j∈_,_)=O[_] _; refine IsBigO.sum fun i _=> (?_); simpa only [Pi.one_apply,one_mul,mul_one,one_pow] using! ((hx.pow i).mul (cost (L:=L) W K M s h i x)) -- expand buys

variable {T T':ι→Point G d n} {x y:ι→Tags G d n}
lemma cash (h:Roi U)(v:τ=O[L] (1:ι→ℝ))(h1:∀ i:Fin n,Salary ℂ L 1 (fun j=>x j i))(h2:∀ i:Fin n,Salary ℂ L 1 (fun j=>y j i))(z:∀ i:Fin n,Discount ℂ L p (fun j=> x j i-y j i)) (k:ℕ): Serves L (fun i w=>mote D k w (τ i) (x i)) (fun i w=>mote D k w (τ i) (y i)) U p:=by
     let V'(u:ι×Points n): Point G d n:=∑ i∈Finset.range (k+1), ((τ u.1:ℂ)^ i) • Jury.fxt D u.2 i
     have he(i:ι×Points n)(v:Tags G d n): V' i v= mote D k i.2 (τ i.1) v:=by unfold V' mote; rw [_root_.sum_apply]; rfl
     let Y:= diners L U; refine banquet.mpr ((matPays (Q:=V') (v:=y∘Prod.fst) (p:=x∘Prod.fst) (l:=Y) (fun a=>?_ ) (fun i u=> (h2 i u).comp_tendsto plot_le) (fun i u=>(h1 i u).comp_tendsto plot_le) (fun i u=>(z i u).comp_tendsto plot_le)).congr_left fun i=>?_); · simp_rw [he]; exact price W K M s h k a v
     rw [he,he]; rfl
end YM.SignedWilsonExpansion.Belle.Path
