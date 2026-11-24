import YM.WilsonCoeffUV.Product.Connected.Thermo
/-!
# Mixed price domains; costs per deterministic root
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n c:Side}{U V α β:Type*}{r h D j e i l k:ℕ}{A B C s:ℝ}{G:Gauge}
abbrev ProfileW := Cover→ ℕ
def Ridge (v:ProfileW)(x:dock Cover α r):= Finset.univ.sup fun i=> v (x i).1
lemma Ridge.host (v:ProfileW)(x:dock Cover α r)(i): v (x i).1≤ Ridge v x:= Finset.le_sup (f:=fun i=>v (x i).1) (Finset.mem_univ i)
lemma Ridge.cap {v:ProfileW}{x:dock Cover α r}{i':ℕ}(p:∀ i,v (x i).1 ≤ i'): Ridge v x≤ i':= Finset.sup_le fun i _=> p i
lemma Ridge.turn (v:ProfileW)(x:dock Cover α r)(p:Equiv.Perm (Fin r)): Ridge v (x∘p)=Ridge v x:=by
    refine le_antisymm (Ridge.cap (fun i=> Ridge.host v x (p i))) (Ridge.cap (fun i=>?_)); obtain ⟨i,rfl⟩:= p.surjective i; exact Ridge.host v (x∘p) i

variable {u:ℕ}{w:ProfileW}
abbrev quoteT (v:ProfileW)(u:ℕ)(x:dock Cover α r):ℝ:= autumn 1 u (Ridge v x)
lemma quoteT_pos (x:dock Cover α r)(v:ProfileW)(u:ℕ):1≤quoteT v u x:= autumn_pos zero_le_one ..
abbrev billR (w:ProfileW)(u:ℕ)(x:dock Cover α r):= quoteT w u x
-- max jump separately (common indicating DIFFERENT roots, not translation-free)
lemma quote_less (p w:ProfileW)(t:p≤w)(x:dock Cover α r): quoteT p u x≤quoteT w u x:= autumn_mono zero_le_one _ (Ridge.cap (fun i=> (t _).trans (Ridge.host w x i)))
lemma quote_turn (u)(w:ProfileW)(x:dock Cover α r)(p:Equiv.Perm (Fin r)): quoteT w u (x ∘ p)=quoteT w u x := by unfold quoteT; rw [Ridge.turn]
def AngleSea (w:ProfileW): Prop := ∀ i j,w i ≤ w j+Bank.terrain.gap j i

-- rails current
section
variable [NormedAddCommGroup V]
abbrev Rent (p:ProfileW)(u:ℕ)(X:Ten V (Cloth α) r)(A:ℝ): Prop:= Award X (quoteT p u) A
variable {P:Ten V (Cloth α) r}{p:ProfileW}
lemma Rent.spin (h:Rent p u P A)(q: Equiv.Perm (Fin r)): Rent p u (fun x=>P (x∘q)) A:= Award.pivot h (q.symm.arrowCongr (Equiv.refl _)) rfl (funext (fun j=> quote_turn u p j q))
lemma Rent.swirl [NormedSpace ℝ V](h:Rent p u P A): Rent p u (swirl P) A:=by
    let C:ℝ:= Fintype.card (Equiv.Perm (Fin r)); have hc:0<C:=by unfold C; positivity
    have hp:= (Award.sum (w:=fun _=> A) (S:=Finset.univ) (fun i _=> h.spin i) (fun x=>zero_le_one.trans (quoteT_pos x ..))).μ C⁻¹; rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,abs_of_pos (inv_pos.mpr hc)] at hp; change Rent p u (Blue.swirl P) (C⁻¹*(C*A)) at hp; rwa [inv_mul_cancel_left₀ hc.ne'] at hp
abbrev RentX (p:ProfileW) (u:ℕ)(P:canal Cover α β V k r)(A:ℝ): Prop:= Award (fun i:dock Cover β r×dock Cover α k=>P i.1 i.2) (fun i=>quoteT p u i.1) A
variable {M N:canal Cover α β V k r}
lemma RentX.take (v:RentX p u M A) : Rent p u (ruins M) A:= Award.cell (f:=M) v (fun i=>quoteT_pos i p _)
lemma RentX.turn (h:RentX p u M A)(q:Equiv.Perm (Fin r)): RentX p u (fun x y=>M (x ∘ q) y) A:= Award.pivot h ((q.symm.arrowCongr (Equiv.refl (Cloth β))).prodCongr (Equiv.refl _)) rfl (funext fun i=>quote_turn u p i.1 q)
lemma RentX.plus (v:RentX p u M A)(h:RentX p u N B): RentX p u (M+N) (A+B):= Award.plus v h (fun i=> zero_le_one.trans (quoteT_pos i.1 ..))
lemma RentX.crew [NormedSpace ℝ V] {P:canal Cover α α V 2 r}(p:RentX w u P A): RentX w u (swivel P) A:=by
    let C:ℝ:= Fintype.card (Equiv.Perm (Fin r)); have hc:0<C:=by unfold C; positivity
    have he:= (Award.sum (S:=Finset.univ) (fun i _=> p.turn i) (fun x=>zero_le_one.trans (quoteT_pos _ ..))).μ C⁻¹; rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,abs_of_pos (show 0<C⁻¹ by positivity)] at he
    rw [show (Fintype.card _:ℝ)=C from rfl,inv_mul_cancel_left₀ hc.ne'] at he; unfold RentX; convert! he using 1; funext x; simp only [swivel,Pi.smul_apply,Finset.sum_apply]; rfl
lemma RentX.smear (p:RentX w u M A)(x): Summable (fun y=>‖M x y‖):= ((summable_prod_of_nonneg (fun i:dock Cover β r×dock Cover α k=> norm_nonneg (M i.1 i.2))).mp (Award.sumnorm p (fun _i=>quoteT_pos _ ..))).1 x
lemma RentX.minus [CompleteSpace V](h:RentX w u M A)(p:RentX w u N B): ruins (M-N)=ruins M-ruins N:=funext fun x=> (h.smear x).of_norm.tsum_sub (p.smear x).of_norm
end

-- product weights later aggregate
lemma quote_walk (u:ℕ){x:dock Cover α i}{y:dock Cover β i}(p:AngleSea w): quoteT w u y≤ quoteT w u x*∏ i,autumn 1 u (Bank.terrain.gap (x i).1 (y i).1):= by
    have he:Ridge w y≤Ridge w x+∑ i,Bank.terrain.gap (x i).1 (y i).1:= Ridge.cap (fun i=> (p _ _).trans (add_le_add (Ridge.host _ _ i) (Finset.single_le_sum (fun i _=> Nat.zero_le (Bank.terrain.gap (x i).1 (y i).1)) (Finset.mem_univ i))))
    exact (autumn_mono zero_le_one u he).trans ((autumn_tax zero_le_one ..).trans (mul_le_mul_of_nonneg_left (row_fold _ _ zero_le_one _) (zero_le_one.trans (quoteT_pos x ..))))
lemma recipeG (w:ProfileW)(L:Side)(x:dock Cover (Co L α) i)(u): quoteT w u x= quoteT (fun i=>w (parentC L i)) u (panel L α ∘ x):=by
    unfold quoteT Ridge; congr 2; funext i; rw [Function.comp_apply]; congr 1; rw [parent_pack]
lemma portStand [NormedAddCommGroup V]{L:Side}{P:Gen V (Cloth α)}(h:Rent (fun i=>w (parentC L i)) u (P i) A): Rent w u (bend (panel L α).symm P i) A:=by
    let b:= (Equiv.refl (Fin i)).arrowCongr (panel L α); exact Award.pivot h b rfl (funext (fun x=> Eq.symm (recipeG w L x u)))
end YM.WilsonCoeffUV.Mer
