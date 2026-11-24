import YangMills.WilsonProof.NativeSupport.Commissioned140.AppointedOrdinaryScope.Subarray
/-!
# Additional convenience: c through h unchanged when using a Near proper-subarray

Here we generalize local uniqueness in the original FAR identification from Match; compare against
our mixed stationary reads. Thus even Near with unit fields permits use of **this same packet**,
not renaming OPE to a different V. Equality on conf, including empty arity.
No physical prices in this proof either.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar.Loft
open Finset Function Filter Set PowerSeries XSpace XSpace.Normalize XSpace.Structure1 Scale O O.Score
open Register Dframe O O.Score O.Enh O.Bind
open MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open scoped Topology BigOperators Classical
variable {G:Gauge} {n m l p k n' h:ℕ} (N:WilsonPrescription G){hG:G.Simple}
    {Z:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{σ:Prescription (Press.portDeck G)} (H:Main.Match N hG Z σ true)
local notation "A"=> Scale.Measure.outlook N.scheme N.criterion
local notation "Ω"=> install A
local notation "V"=> PowerSeries ℂ
variable {d:Fin n→ℕ} (u: AppointedH140Inputs G d)
-- linearization uniqueness, fixed x. Enough on singleton compacts.
variable {S:Set (Points m)} {x:Points n} (hx:x∈ conf n)
def porch (x:Points n)(y:Points m)(v:Scan G m):V:=∑ a:Picks G d, PowerSeries.C (multipliers u a) * party Ω x y (indexScan a) v
include H
lemma onto {e:Fin m→ℕ}(hd: AppointedH140Through l d)(he: AppointedH140Through l e)(v:Scan G m)(hv: InCaps e v)(x:Points n)(y:Points m)(k:ℕ):
    coeff k (porch N u x y v)= rawCoeff A hd he (forest x y) k u (loadScan v hv):= by
 simp_rw [porch, map_sum (coeff k), coeff_C_mul]; rw [basis_sum (rawCoeff ..) u,_root_.sum_apply]; apply Finset.sum_congr rfl; intro i hi
 exact congrArg (fun b:ℂ=> multipliers u i * b) (rawCoeff_on_scan _ (H.separatedOPE 0).wilson.dimensions hd he (indexScan i) v (boundedByCaps i) hv (forest x y) k).symm
omit H in
lemma penitent (v:Scan G m) (x: Points n)(y:Points m)(h:ℕ) :
    Lamp Ω h y v (ope A u x) = ∑ a:Picks G d, PowerSeries.C (multipliers u a) * Lamp Ω h y v (Canon.FarCoefficients A (indexScan a) x):=by
 simp_rw [←LampT, ope,sum_mul,mul_assoc,mul_sum]; rw [sum_comm]
-- transfer of an eventual equality (all x)
omit H in
lemma carry {I:Type}{f g:I→ℝ→V}{r:ℝ} (h:∀ᶠ t:ℝ in atTop,∀ i,f i t=g i t)(hf:ChargeP p r f): ChargeP p r g:= by
 intro i hi; exact Rain.raise (hf i hi) (h.mono fun t ht x=> le_of_eq (by rw [ht x]))
def Served (x:Points n)(f:Q G→V)(p h:ℕ): Prop:= ∀ m (S:Set (Points m))(v:Scan G m), IsCompact S → S ⊆ Outside m →
    ChargeP p ((h:ℝ)+1+(totalG v:ℝ)) (fun (y:↥S) t=> porch N u x (squeeze (-t) y.val) v- Lamp Ω h (squeeze (-t) y.val) v f)
include hx
lemma priced : Served N u x (ope A u x) p h:= by
 intro m S v hS hz; have hw:= (H.separatedOPE 0).wilson; let x': ↥({x}:Set (Points n)):=⟨x,Set.mem_singleton _⟩
 have H' (i:Picks G d) := (hw.far (indexScan i)).2.2 {x} isCompact_singleton (singleton_subset_iff.mpr hx) h p m S v hS hz; simp_rw [penitent N,porch,← sum_sub_distrib,← mul_sub]
 exact ChargeP.sum Finset.univ (fun i _=> ChargeP.times (ChargeP.fixed _) (ChargeP.pull (H' i) (fun y:↥S=> (x',y))))
-- fixed shape uniqueness by local `Fiasco`. Needn't control a derivative of Faro in conf.
lemma represents {ψ:Q G→V} (H':Served N u x ψ p h) (b:Q G)(hh:heft b ≤ h)(hx': k<p) : coeff k (ψ b) = coeff k (ope A u x b):= by
 let Hπ := (H.separatedOPE 0).wilson
 let f:=ope A u x; let v:Scan G n:=fun _=> b; let F:=Canon.FarCoefficients A v; let D:Fable G n:=fun y a=> F y a+(ψ a - f a); let K:Set (Points n):={x}
 have hF:Fiasco Ω K h 1 p v F:= (Hπ.far v).2.2 K isCompact_singleton (singleton_subset_iff.mpr hx) h p
 have hD:Fiasco Ω K h 1 p v D:= by
    intro m S w hS hv; let T (Q:↥S)(t:ℝ):= squeeze (-t) Q.val; let Gt(f)(Q:↥S)(t:ℝ):=porch N u x (T Q t) w-Lamp Ω h (T Q t) w f
    have he (y:Points m): Lamp Ω h y w (D x) = Lamp Ω h y w (F x) + (Lamp Ω h y w ψ - Lamp Ω h y w f):= by
       simp_rw [← LampT,D,add_mul,sub_mul, sum_add_distrib, sum_sub_distrib]
    apply carry _ (ChargeP.plus (hF m S w hS hv) (ChargeP.pull (ChargeP.sub (H' m S w hS hv) (priced N H u hx m S w hS hv)) Prod.snd))
    apply Eventually.of_forall; intro t p; have ht : (p.1.val: Points n)=x:= Set.mem_singleton_iff.mp p.1.property; dsimp only [Basket, Function.comp_apply]; rw [ht,he]; change _= party _ _ _ _ _-(Lamp _ _ _ _ _+ (Lamp _ _ _ _ _ - Lamp _ _ _ _ f)); unfold f; abel
 have hd:PlainF K D h p:=by
    intro v hv k _; refine ⟨‖coeff k (D x v)‖,fun y=> by dsimp only; rw [Set.mem_singleton_iff.mp y.property]⟩
 obtain he:= uniqueK Hπ.scope Hπ.dimensions Hπ.wardRank Hπ.awake zero_lt_one le_rfl hF hD (philosophy (Hπ.far v).2.1 isCompact_singleton
    (singleton_subset_iff.mpr hx)) hd x (Set.mem_singleton _) b hh k hx'
 unfold D at he; rw [map_add,map_sub] at he; exact sub_eq_zero.mp ((left_eq_add.mp he))
variable (φ:Fin n' ↪ Fin n)
omit hx in
lemma porch_units (x:Points n)(y:Points m)(hv:∀ i,i∉Set.range φ→u i = leaf G (d i))(hh:forest x y ∈ conf (n+m)) (v: Scan G m):
    porch N u x y v = porch N (d:=fun i=>d (φ i)) (fun i=> u (φ i)) (keptPoints φ x) y v:=by
 ext1 k; let e(i:Fin m):= heft (v i); obtain ⟨l,hd'⟩:= Finite.exists_le (Sum.elim d e); let U:InCaps e v:=fun _=> le_rfl
 have hd:AppointedH140Through l d:=fun i=> hd' (Sum.inl i); have he:AppointedH140Through l e:= fun i=>hd' (Sum.inr i)
 let Q:= Embedding.refl (Fin m); let t:=squeeze 0 y; have hp: squeeze 0 y=y:= by rw [squeeze, neg_zero, Real.exp_zero,one_smul]
 rw [onto N H u hd he v U,onto N H _ (fun i=> hd (φ i)) he v U]; obtain hr:= raw_unit_drop N Z H hd he φ Q 0 x y (by rw [hp]; exact hh) (u:=u) (v:=loadScan v U) hv (fun i hi=>False.elim (hi ⟨i,rfl⟩)) (k:=k) -- remaining args
 simp_rw [show keptPoints Q y=y from (by ext;rfl),hp] at hr; exact hr
-- independent; same for suppressed fields of c as argument of M.2. Never substitute a new Far program.
lemma ope_preserved (hv:∀ i, i∉ Set.range φ→u i=leaf G (d i)): ope A u x=ope A (d:=fun i=>d (φ i)) (fun i=> u (φ i)) (keptPoints φ x) := by
 let f:= ope A (d:=fun i=>d (φ i)) (fun i=>u (φ i)) (keptPoints φ x); have hF(p h:ℕ) : Served N u x f p h:= by
    intro m S v hS hz; refine carry ?_ (priced N H (kept_conf φ hx) m S v hS hz (d:=fun i=> d (φ i)) (u:=fun i=> u (φ i)))
    filter_upwards [layout_eventually (K:={x}) isCompact_singleton (singleton_subset_iff.mpr hx) hS hz] with t ht p
    rw [porch_units N H u φ _ _ hv (ht _ (Set.mem_singleton _) _ p.property).1]
 funext b; ext1 k; exact (represents N H u hx (hF (k+1) (heft b)) b le_rfl (Nat.lt_succ_self _)).symm
lemma proper_vector (hv:∀ i, i∉ Set.range φ→u i=leaf G (d i))(z:ℝ):
    croppedVector A h p u x z=croppedVector A h p (d:=fun i=>d (φ i)) (fun i=> u (φ i)) (keptPoints φ x) z:=by
 unfold croppedVector; rw [ope_preserved N H u hx φ hv]
end YM.FVA2.GradedFar.Loft
