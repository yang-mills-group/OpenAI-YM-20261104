import YM.FormalBulk08.Kemp.Sink

/-! Root limits of ritual assertions. Quantify interactions comparing
two RHS/LHS series separately. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Kemp
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries
open Lotus Shore Mesa Gorge City Cork Rift
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {I J : Type*} {r:ℕ} (n:Side)
abbrev Yard (v : chain (Tor n I) r) := {t:chain (Biglot I) r // Lotus.drip n ∘ t=v}

def shedSpace (v:chain (Tor n I) r) : Jolt (Yard n v) (fun m=>Ride m n v) where
    give m u:=⟨Lotus.drip (m*n) ∘ u.val,funext fun j=>(tray_drip m n (u.val j)).trans (congr_fun u.property j)⟩
    undo m x:=⟨boil (m*n)∘ x.val,funext fun j=>by rw [Function.comp_apply,comp_apply, ←tray_drip m n, drip_boil]; exact congr_fun x.property j⟩
    back _ _:=Subtype.ext (funext fun j=>drip_boil ..)
    tame x:= (eventually_all.mpr fun i=> (onward n).eventually (boil_drip (x.val i))).mono fun _ h=> Subtype.ext (funext fun i=> h i)

variable [Fintype I]
lemma sieve_copy {T : Tile (Biglot I) r}{S : (m:Side)→ Tile (Tor m I) r}{x:Biglot I}{η : ℝ} (h:Kalm η x T S)(he:0<η) (v: chain (Tor n I) r): Tendsto (fun m=>cores (tray m n) (S (m*n)) v) atTop (𝓝 (sieve n T v)) := by
   simp_rw [core_sum,_root_.YM.FormalBulk08.Kemp.sieve];let Y:=Yard n v
   obtain ⟨h,C,H⟩:=h; let p:=η/(r+1); let D:=shedSpace n v
   let U:= size x.1;have hp : 0<p:=by unfold p; positivity
   have hC:= H.exists.choose_spec.1
   let F (i:Y):= Real.exp (η*U)*C*∏ j,coast p (i.val j)
   refine jolt_limit D (fun m w=> S (m*n) w.val) (fun z=>T z.val) F (((monsoon (r:=r) (I:=I) hp).comp_injective (i:=fun u:Y=>u.val) Subtype.val_injective).mul_left _) (fun i=>mul_nonneg (mul_nonneg (Real.exp_pos _).le hC) (Finset.prod_nonneg fun _ _=>(Real.exp_pos _).le)) (fun y=> (h y.val).comp (onward n)) ?_
   filter_upwards [(onward n).eventually H] with m hm u
   let T1:=S (m*n) u.val; let q:= Lotus.drip (m*n) x;let R : chain (Tor (m*n) I) (r+1):=Fin.cons q u.val
   let K:=wide (lake (m*n) I) R; have he' : ‖T1‖*Real.exp (η*K) ≤ C:=penn_chill _ hm
   let t:=D.undo m u
   have hz : (∑ i,size (t.val i).1) ≤ (r+1)*(K+U):= by
       have h (i): size (t.val i).1 ≤ K+U := (skit_anchor (m*n) R 0 i.succ).trans (Nat.add_le_add_left (skirt ..) K)
       refine (Finset.sum_le_sum (fun i _=> h i)).trans ?_; simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fin]; exact Nat.mul_le_mul_right _ (Nat.le_succ _)
   change ‖T1‖≤Real.exp _*C* (∏ j,coast p (t.val j)); rw [prod_shine t.val]
   let d:=∑ i,size (t.val i).1
   have hy: p*(d:ℝ) ≤ η*((K:ℝ)+(U:ℝ)):= by
       have hh : (d:ℝ) ≤ (r+1:ℝ)*((K:ℝ)+(U:ℝ)):=by exact_mod_cast hz
       refine (mul_le_mul_of_nonneg_left hh hp.le).trans_eq ?_; unfold p; field_simp
   calc
       ‖T1‖ = (‖T1‖* Real.exp (η*K))*Real.exp (-η*K) := by rw [mul_assoc,←Real.exp_add,neg_mul,add_neg_cancel, Real.exp_zero,mul_one]
       _ ≤ C*Real.exp (-η*K):=mul_le_mul_of_nonneg_right he' (Real.exp_pos _).le
       _ ≤ _ := by rw [mul_comm _ C, mul_assoc,←Real.exp_add]; apply mul_le_mul_of_nonneg_left _ hC;apply Real.exp_monotone;change -η*K ≤ η*U+ -p*(d:ℝ);nlinarith
lemma copy_singleton (p:(m:Side)→Pap (Tor m I)){T:Tile (Biglot I) r} (U:Pap (Tor n I))(e:ℕ){x:Biglot I}{η : ℝ}(h:Kalm η x T (fun m=>rancho (p m) e r))(he : 0<η)(hr:rancho U e r=sieve n T)(v:chain (Tor n I) r): Tendsto (fun m=>rancho (shrink (n:=n) (p (m*n))) e r v) atTop (𝓝 (rancho U e r v)) := by
   rw [hr]; apply (sieve_copy n h he v).congr'; refine .of_forall fun m=>?_ ; simp only [shrink,rancho,coeff_map]; rw [AlgHom.toRingHom_eq_coe,RingHom.coe_coe,pebble]

-- arbitrary Pap weighted only if ALL ranks converge. Incl 0.
lemma trinket (m j : ℕ) (a : I→Pap J) (d : J→₀ℕ) (p : Side→Pap I) (t : Pap I)
    (N : ℕ) (he : ∀ᶠ n in atTop, ∀ l,N<l → marble l (coeff j (p n))=0) (ht : ∀ l,N<l→marble l (coeff j t)=0)
    (h : ∀ r v,Tendsto (fun n=> marble r (coeff j (p n)) v) atTop (𝓝 (marble r (coeff j t) v))) :
    let f(F:TypeR I) := MvPolynomial.coeff d (coeff m (insertAt ℝ a F*X^j));
    Tendsto (fun n=> f (coeff j (p n))) atTop (𝓝 (f (coeff j t))) := by
   intro f
   have hf (P : TypeR I) (H : ∀ l,N<l→ marble l P=0) : f P = ∑ i∈ (Finset.range (N+1)),∑ v:chain I i, marble i P v * f (cards v) := by
      have hz F G : f (F+G)=f F+f G := by unfold f; rw [map_add,add_mul,map_add,MvPolynomial.coeff_add]
      let F : TypeR I →+ ℝ:={toFun:=f,map_add':=hz,map_zero':=by simp [f]}
      have hu l (A : Tile I l) : f (facade l A)=∑ v:chain I l,A v * f (cards v):= by
         change F (facade l A)= _; rw [facade_eq,map_sum]; apply Finset.sum_congr rfl; intro v _
         change f _=_; unfold f; simp only [_root_.map_mul, insert_C, mul_assoc]; rw [coeff_C_mul];simp
      change F P=_; nth_rw 1 [←crema P N H]; rw [map_sum];exact Finset.sum_congr rfl fun i _=> hu i _
   rw [hf _ ht]; exact (tendsto_finsetSum _ (f:=fun i n=>∑ v:chain I i,(marble i (coeff j (p n)) v)*f (cards v)) (fun i _=>tendsto_finsetSum _ (fun v _=> ((h _ v).mul_const _)))).congr' (he.mono (fun _ hh=>Eq.symm (hf _ hh)))
lemma keepsake (p: Side→Pap I)(q: Pap I)(a: I→ Pap J)(N : ℕ→ℕ)
    (he : ∀ j,∀ᶠ n in atTop, ∀ l,N j<l→ rancho (p n) j l=0)
    (h : ∀ j r v,Tendsto (fun n=>rancho (p n) j r v) atTop (𝓝 (rancho q j r v))) (m : ℕ)(v:J→₀ℕ):
    Tendsto (fun n=>MvPolynomial.coeff v (coeff m (roam ℝ a (p n)))) atTop (𝓝 (MvPolynomial.coeff v (coeff m (roam ℝ a q)))) := by
    have hT (j l) (hl : N j<l): marble l (coeff j q)=0:= funext fun v=> tendsto_nhds_unique (h _ _ v) (tendsto_const_nhds.congr' ((he j).mono (fun _ hh=>congr_fun (hh l hl).symm v)))
    have hh (T:Pap I): MvPolynomial.coeff v (coeff m (roam ℝ a T))=∑ j∈Finset.range (m+1), MvPolynomial.coeff v (coeff m (insertAt ℝ a (coeff j T)*X^j)):=by unfold roam; rw [(liquid _ _ m).apex,map_sum,MvPolynomial.coeff_sum]
    simp_rw [hh]; exact tendsto_finsetSum _ (fun j _=>trinket m j a v p q (N j) (he j) (hT j) (h j))
end YM.FormalBulk08.Kemp
