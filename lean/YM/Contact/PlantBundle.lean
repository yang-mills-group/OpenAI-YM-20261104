import YM.Contact.HarvestNodes
import YM.Push.RELAY_DIFFERENCE.Placement

/-! Offsetting and planting already billed centered literal cylinders. -/
noncomputable section
set_option autoImplicit false
namespace YM.MergeProof.Ribbons
open Function Filter Set Lattice Wilson RG Cells Extraction Push Push.RelayDifference
open scoped BigOperators Topology Classical
variable {G:Gauge}{Q:Schedule}{p N J:ℕ} {β A:ℝ}
local notation "n"=>Q.side N p
structure BlockCost (F : Config G (Q.side N p)→ℂ) (J:ℕ) (β A:ℝ):Prop where
    stop:J≤N
    safe: Interior ((center Q p stop 0).chamber 0) F
    amount: (center Q p stop 0).rootTest β F ≤ A
lemma shift_literal (b:Bool)(s:Signed)(f: Config G (Q.side N p)→ℂ):literal (RelayDifference.oriented f b s):=by
   intro i j; funext V
   have h:pull s (i+j) V = pull s i (translate j V):=by
      rw [←pull_one, pull_pull]; rw [one_mul]; rfl
   simp only [RelayDifference.oriented, comp_apply,h]
variable {F : Config G (Q.side N p)→ℂ} (h:BlockCost (Q:=Q) (p:=p) (N:=N) F J β A)
lemma BlockCost.displaced {T:Tiling (Q.side N p)} {o:Site (Q.side N p)}{v:T.Cell}
    (hp:Cells.span Q h.stop p ∣ T.side.val) (ht:o∈T.margin v (3*Cells.span Q h.stop p)) {s:Signed}(hi:diag s)(b:Bool)(hs: Seam G (Q.side N p) β) : ∃ U:Config G (Q.side N p) →ℂ, T.copy v U=RelayDifference.oriented F b s o ∧ Interior (T.chamber 0) U∧ T.rootTest β U ≤ A :=by
      obtain ⟨x,hx⟩:=T.pointed v o; let g:=T.omega v; have hd:diag g:=rfl
      let b':=(decide (T.hand v)).xor b;have hu : ((decide (T.hand v)).xor b')= b :=by unfold b';cases (decide (T.hand v)) <;> cases b <;> rfl
      let r:=g⁻¹*s;have hG:g*r=s:=by unfold r; rw [← mul_assoc,mul_inv_cancel, one_mul]
      have hr:diag r:=diag_mul (diag_inv hd) hi
      refine ⟨(RelayDifference.oriented F b' r x), (by rw [copied];rw [hu,hG,hx]),?_⟩
      refine offset h.stop T β A hp (shift_literal b' r F) hs (center_interior h.stop r hr b' 0 h.safe) ((center_price h.stop 0 F b' r hr h.safe β).le.trans h.amount) (?_) -- argument order
      exact (T.reflected_margin x v _).mpr (hx.symm ▸ ht) -- Eq.symm wrong?
include h in
lemma BlockCost.positive:0≤A:= (Tiling.root_nonneg _ _ F).trans h.amount

lemma permute_margin (T:Tiling (Q.side N p)) (x:Site (Q.side N p)) (s:Site T.period)(k:ℕ)(h:x∈T.margin (T.which x) k): x+T.units.embed s∈ T.margin (T.which (x+T.units.embed s)) k:=by
     have hz (u: Site (Q.side N p))(i:Axis): T.coordinated (T.which u) u i = ZMod.val (T.hom (u i - T.base i)):= by
         rw [T.residual]
         unfold Tiling.residue Tiling.grid
         conv_rhs => rw [← ZMod.natCast_zmod_val (u i - T.base i),map_natCast,ZMod.val_natCast]
     have hv(i:Axis): T.coordinated (T.which (x+T.units.embed s)) (x+T.units.embed s) i= T.coordinated (T.which x) x i:= by
         rw [hz,hz]
         congr 1
         change T.hom ((x i + (↑((T.units.count.val:ℤ)*(s i).valMinAbs)))-T.base i)=T.hom _
         rw [show T.units.count=T.side by rfl, add_sub_right_comm, map_add, map_intCast, Int.cast_mul, Int.cast_natCast,ZMod.natCast_self,zero_mul,add_zero]
     exact ⟨fun i=> by change T.kind.Strict _ (T.coordinated _ _ i); rw [hv]; exact h.1 i, fun i=> by rw [hv i]; exact h.2 i⟩

/-- Perturbation by small literal shifts preserves quantitative margin. -/
theorem perturb_cell {n':Side}(T:Tiling n'){x:Site n'}{v:T.Cell}{k l:ℕ}(h: x∈ T.margin v (k+l+1)) {a : Cover}(ha:∀ i:Axis,(a i).natAbs≤l) : x+wrap n' a∈T.margin v k :=by
    have hc : x+wrap n' a∈T.chamber v:= add_comm _ (wrap n' a) ▸ T.fits_stencil h (fun i=> (ha i).trans_lt (by omega)) -- omega k
    refine ⟨hc,fun i=> ?_⟩
    let d:=T.coordinated v x i; let t:ℤ:=(d:ℤ)+a i; obtain ⟨hx,hx'⟩:= h.2 i; change k+l+1≤d at hx
    change d+(k+l+1)+T.kind.shift ≤ T.side.val at hx';have he':=ha i
    have h0:(k:ℤ) ≤ t:=by unfold t; omega
    have h2:t+(k:ℤ)+(T.kind.shift:ℤ) < T.side.val:=by unfold t; omega
    rw [show T.coordinated v (x+wrap n' a) i=t.toNat from ?_]
    · omega
    rw [Tiling.coordinated, show (x+wrap n' a) i - T.starts v i=(t.toNat:Per n') from ?_]
    · exact ZMod.val_natCast_of_lt (by have ht:=T.narrow; omega)
    change x i+(↑(a i):Per n') - T.starts v i=(t.toNat:Per n')
    rw [add_sub_right_comm,←Int.cast_natCast,Int.toNat_of_nonneg (show 0≤t from by omega),Int.cast_add]
    dsimp [d]; rw [Int.cast_natCast,Tiling.coordinated,ZMod.natCast_zmod_val]

lemma inherits_ratio {C:Family G} {F:Extraction.Order} {m k:ℕ}(h:m≤k):∀ᶠ t:ℕ×ℕ in F.fuse, ∃ g:k ≤ t.1,Cells.span C.S g t.2 ∣ Cells.span C.S (h.trans g) t.2:=by
     rw [Extraction.Order.fused, Extraction.Order.late]; dsimp
     filter_upwards with i
     filter_upwards [F.mesh.cofinal.eventually (eventually_ge_atTop k)] with j hj
     exact ⟨hj,Around.inherits h hj⟩
variable {C: Family G}{I:Type*}[Fintype I]{N p k m:ℕ}
set_option quotPrecheck false
lemma plant_typed (Gx:I → Config G (C.side N p) →ℂ) (y:I→Site (C.side N p))(orient:I→Bool)(turn:I→Signed)(A:I→ℝ) (paid:∀ i,BlockCost (Q:=C.S) (N:=N) (p:=p) (Gx i) k (C.beta N p) (A i)) (gdiag:∀ i,diag (turn i)) (hk:k ≤ N)(h:m≤k) (holds:Seam G (C.side N p) (C.beta N p))
     (clear:∀ (T:Tiling (C.side N p)),T.side.val=Cells.span C.S (h.trans hk) p → (∀ i,y i∈T.chamber (T.which (y i))) →∀ i j:I, T.which (y i)=T.which (y j)→i=j) (placed:∃ T:Tiling (C.side N p),T.side.val=Cells.span C.S (h.trans hk) p∧∀ i,y i∈T.margin (T.which (y i)) (3*Cells.span C.S hk p)) : ‖moment (C.beta N p) (fun z=>∏ i:I, RelayDifference.oriented (Gx i) (orient i) (turn i) (y i) z)‖ ≤ ∏ i:I, A i := by
        obtain ⟨T,hT,hM⟩:=placed; choose U h1 h2 h3 using fun i=> (paid i).displaced ((Around.inherits h (p:=p) hk).trans (by rw [hT])) (hM i) (gdiag i) (orient i) holds
        simp_rw [← h1]; exact (T.planted holds (fun i=>T.which (y i)) (clear T hT (fun i=>(hM i).1)) U h2).trans (Finset.prod_le_prod (f:=fun i=>T.rootTest (C.beta N p) (U i)) (g:=fun i=>A i) (fun i _=> T.root_nonneg _ _) (fun i _=> h3 i))

theorem place_together {y:I→Site (C.side N p)}(hk:k≤N)(h:m≤k){nI q':ℕ} (hsize:nI*(2*(3*q'+q'+1))< (center C.S p (h.trans hk) 0).side.val) (hspan:Cells.span C.S hk p≤q') (ι: I→Fin nI) (z:Fin nI→Site (C.side N p)) (p':I→Site (C.side m p)) (a:I → Cover) (hx:∀ i,y i=z (ι i)+(C.S.toDepth (h.trans hk) p).embed (p' i)+wrap (C.side N p) (a i)) (ha:∀ i l,(a i l).natAbs≤q'):∃ T:Tiling (C.side N p),T.side.val=Cells.span C.S (h.trans hk) p∧∀ i,y i∈T.margin (T.which (y i)) (3*Cells.span C.S hk p):=by
      let T:=(center C.S p (h.trans hk) 0); obtain ⟨o,ho⟩:= T.fits_together z _ (by omega:0<3*q'+q'+1) hsize; let X:=T.newly o
      refine ⟨X,rfl,fun i=>?_⟩
      rw [hx i]
      have hz:= perturb_cell X (permute_margin X (z (ι i)) (p' i) (3*q'+q'+1) (ho (ι i))) (fun l=> ha i l)
      let ξ := z (ι i)+X.units.embed (p' i)+wrap _ (a i)
      change ξ∈X.margin (X.which ξ) _
      rw [X.which_chamber (hx:=(show ξ∈_ from hz.1))]
      exact Lease.fewer X _ (Nat.mul_le_mul_left _ hspan) hz
end YM.MergeProof.Ribbons
