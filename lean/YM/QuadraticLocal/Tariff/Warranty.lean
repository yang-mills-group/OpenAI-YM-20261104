import YM.QuadraticLocal.Tariff.Scope
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Tariff
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open RG3 RG3.Annuncia RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe Fusion Attached Push.Local
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {p : BudgetPoint}
variable {V W : Type} [DecidableEq V] [Fintype V][DecidableEq W][Fintype W]
variable (u:W→ V) (R: Census V) (o : V→Site n)
local notation "S"=> (Annuncia.Replica u R)
local notation "ϕ"=> ( Annuncia.Replica.bill u R )
variable (γ:(Replica u R).Mode→ℂ)
variable (w:V→ℝ)(hw:∀ i,0<w i)
variable {T J η : Type*} {a b c δ ε :ℝ}{B B' :ℕ}
local notation "ν"=> ( w ∘ u )
open Next.Foundations
variable (g:W→ℂ) (C:W→ℝ)(hC:∀ i, ‖g i‖ ≤ C i)(hP:∀ i,C i≤1)
local notation "ψ"=> ( Replica.sign u R g )
def exposes (T:Set (Replica u R).Mode) (v: (Replica u R).Mode):ℂ:= if v∈T then Replica.sign u R g v else 0
local notation "Ψ"=> ( Tariff.exposes u R g )
def levy (T:Set (Replica u R).Mode) (v:(Replica u R).Mode):ℝ:= if v∈T then ∏ j∈v.val,C j else 0
local notation "κ"=> ( Tariff.levy u R C )
abbrev factor (C:W→ℝ)(s:Finset W): ℝ:= ∏ i∈s,C i
local notation "s!" s:max=> (Tariff.factor C s)
include hC
variable (U:Set (Replica u R).Mode)(V₀: Finset W)
lemma supports (i:(S).Mode): ‖Ψ U i‖ ≤ κ U i:=by
    unfold exposes levy Replica.sign; split; rw [norm_prod]; exact prod_le_prod (fun i _=> norm_nonneg _) (fun i _=>hC i); exact norm_zero.le
lemma purse (s:Finset W) : 0≤ Tariff.factor C s:=by apply prod_nonneg; exact fun i _=> (norm_nonneg _).trans (hC i)
-- Pricing.Agreement.Meta: if Ω>1 analytic factors larger, production receipts must include corresponding Mark budget at greater rate. Don't recover same true ratios for large probes if not making temporary A purchase/summabilities. Serve variant.Need.
variable (ht:∀ v∈U, V₀⊆ v.val)
include hP ht
lemma quotaCap (i:(Replica u R).Mode) : ( Tariff.levy u R C U i ) ≤ Tariff.factor C V₀:=by
    unfold Tariff.levy; split; next h=>
       rw [← Finset.prod_sdiff (ht i h)]; apply mul_le_of_le_one_left (purse g C hC _); exact Finset.prod_le_one (fun i _=> (norm_nonneg _).trans (hC i)) (fun i _=>hP i) -- term? check
    next=> exact purse g C hC _
variable (Δ:T→η)
variable (L:Lamps η J G p (o∘u) (Replica u R))
variable {P : ℕ→ ForcedAddress G n} {F : Code G n} (H: Hard η p P F (o∘u) (Replica u R))
-- keep payments for every Σ slice, truth for Π and λ mixed exps
local notation "M"=> ( Tariff.emit u R o ψ Δ L )
include hw
lemma paysE (h: L.Paid (w∘u) B a b): ( Tariff.emit u R o (Ψ U) Δ L ).Paid w B a ((Tariff.factor C V₀)*b):= Tariff.energy u R o (Ψ U) w hw Δ L ( κ U ) ( supports u R g C hC U ) (quotaCap u R g C hC hP U V₀ ht) (purse g C hC _) h
lemma paysH (h: H.Paid (w∘u) B a b): (Tariff.grains u R o (Ψ U) Δ H).Paid w B a ((Tariff.factor C V₀)*b):= Tariff.token u R o (Ψ U) w hw Δ (κ U) ( supports u R g C hC U ) (quotaCap u R g C hC hP U V₀ ht) (purse g C hC _) H h
omit hC ht hP hw
lemma full : exposes u R g Set.univ=Replica.sign u R g:= by funext; unfold exposes; exact if_pos (Set.mem_univ _)
-- On the full owner set, exposes agrees with Replica.sign.
lemma together (f:Poly S) : pay u R ψ f= pay u R (Ψ U) f+ pay u R (Ψ (Uᶜ)) f:=by
   ext1 i; rw [Poly.part_plus, Tariff.quota,Tariff.quota,Tariff.quota,← sum_add_distrib]; refine sum_congr rfl fun j he=>?_ ; split; next h=> by_cases hp:j∈U <;> simp only [exposes,Set.mem_compl_iff, hp, not_true_eq_false, not_false_eq_true, ↓reduceIte, zero_mul,add_zero, zero_add]
   exact (zero_add _).symm
-- keep label-by-label entries ↑ including locations and derivatives. not canceling between masks. assert exact prefix log crossing selected.T
lemma publication (j:J)(t:T): (Tariff.emit u R o ψ Δ L).nominal t j= (Tariff.emit u R o (Ψ U) Δ L).nominal t j+(Tariff.emit u R o (Ψ (Uᶜ)) Δ L).nominal t j:= by
    unfold emit; simp only [exposes,Set.mem_compl_iff]; split <;> simp_all
-- cross occurrence.K.Layer approximate? Full.
lemma accounts (j:ℕ)(t:T)(y:Config G n): (Tariff.grains u R o ψ Δ H).forced t j y= (Tariff.grains u R o (Ψ U) Δ H).forced t j y+ (Tariff.grains u R o (Ψ (Uᶜ)) Δ H).forced t j y:= together u R g U _
lemma everyday (f:Poly S): Replica.mouth u R g f= (Tariff.pay u R ψ) f:=by ext1 j; rw [ Replica.quota, Tariff.quota ]
-- create full operator with ALL modes. No replacement.We.Core_State.U Phys.Criterion.Work.Atomic.Board.Meta.Pe.Clock.Height.`
variable {R':RG.Rep G n}(E:Gallery η J (o∘u) R' (Replica u R))
def remix : Gallery T J o R' R := ⟨ Tariff.emit u R o ψ Δ E.E, (Tariff.grains u R o ψ Δ E.K).toHard (by apply Tariff.quiet; simp [Replica.sign,Census.quiet]) ⟩
local notation "M'"=> (Tariff.remix u R o g Δ E)
variable (h:E.Pays (w∘u) a b c)
include hw h
include hC hP
lemma attends : M'|>.Pays w a b c:=by
    let h₀_:∀ v∈(Set.univ:Set (Replica u R).Mode),(∅ : Finset W)⊆ v.val:= fun _ _=> Finset.empty_subset _; let he':=(Tariff.full u R g)
    obtain ⟨hv,hp⟩:(emit u R o ψ Δ E.E).Paid w R'.p.B a b ∧ (grains u R o ψ Δ E.K).Paid w R'.p.B a c:=by rw [← he']; simpa only [Tariff.factor, Finset.prod_empty, one_mul] using ( And.intro (paysE u R o w hw g C hC hP _ _ h₀_ Δ E.E h.budget) (paysH u R o w hw g C hC hP _ _ h₀_ Δ E.K h.wages) )
    exact ⟨hv,⟨hp.cover⟩⟩
omit hC hP
lemma associative (ha:0≤a) (t:T)(U':Config G n): ( M' ).density t U'= Replica.mouth u R g (E.density (Δ t) U'):= by
    have he : ( M' ).E.log t U'= Replica.mouth u R g ( E.E.log (Δ t) U') := (Tariff.lightshow u R o ψ w hw Δ E.E h.budget ha t U').trans ( Tariff.everyday u R g _ ).symm
    let k:= Replica.mouth u R g; have hx : ( M' ).gas t U'= k ( E.gas (Δ t) U' ):=by
        change ∑' i, _ = Replica.cable u R g (∑' i, _); rw [( Replica.cable u R g ).map_tsum ( Hard.packet_summing E.K h.wages ha (fun i=> hw (u i)) (Δ t) U' )]; refine tsum_congr fun i=>?_ ; unfold packet; split; next hV=>
           rw [Replica.cable_apply, map_prod ]; refine prod_congr rfl fun j _=>?_ ; exact ( Tariff.everyday u R g _ ).symm
        next=>rw [ map_zero ]
    unfold Gallery.density; rw [ he,hx,Replica.csmul,map_mul, Replica.passed _ _ _ _ ( Lamps.quiet_of_hasSum (Δ t) U' (h.budget.sums ha (fun i=> hw (u i)) ..) ) ]
-- transfer ψ through actual push.S.IsKernel. Integrability will come from bounded real pose Holder.Shape_S.Context.Price.Act_Boot account.N.Scope.E. For any Full lifts.E_P_Runtime.Camera_Field Actor.ψ, use same H. On step.K_Level.
omit hw h
variable {n':Side}{l:ℝ}
open Affinity
lemma moved {L:StepData n' n}(F:Config G n→ Poly S)(hx:L.IsKernel l G)(he:Integrable F (prior G n)): Replica.mouth u R g ∘ L.push l F=L.push l (Replica.mouth u R g ∘ F):= by
    let p':=( Replica.cable u R g ).restrictScalars ℝ
    change p' ∘ _= L.push l (p'∘ F); funext v; have hp:=L.push_slice hx v _ he; unfold StepData.push; rw [Function.comp_apply,← p'.integral_comp_comm hp]; refine integral_congr_ae (ae_of_all _ fun x=> p'.map_smul ..)
end YM.QuadraticLocal.Tariff
