import YM.FormalBulk08.Chapel.Film

/-! Inherited row contraction without a lifted cochain. Keep pre/post data
on the money statements. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Chapel
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries Next.Free RG Precision
open Lotus Shore Mesa Gorge City Cork Rift Lava
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge}{σ η A B C : ℝ}{m r:ℕ}{L : Side}{I J : Type}

-- doesn't need translation
lemma knox_frame {V:Type*}(D:Reach V){T:Tile V (m+1)}(h:Agate T)(hp:∀ a, Knoxville D η a (Lava.shed T a) C)(hc:0≤C): Bail D η T C := by
    refine ⟨hc,fun i a=>?_⟩; let s:=Equiv.swap (0:Fin (m+1)) i;let f (u:pack i a):chain V m:=Fin.tail (u.val∘s);have he (u:pack i a): Fin.cons a (f u) = u.val ∘ s:= by ext1 j;cases j using Fin.cases <;> simp [s,f,u.property,Fin.tail]
    have hf: Injective f:= by
       intro u v hh; apply Subtype.ext;funext j; have H:u.val∘s=v.val∘s := by rw [← he,←he,hh]
       simpa using congr_fun H (s.symm j)
    apply le_trans (b:=∑' u:pack i a, glitter D η T (Fin.cons a (f u))) ?_ ((ENNReal.tsum_comp_le_tsum_of_injective hf (fun v=> glitter D η T (Fin.cons a v))).trans (hp a).2)
    refine le_of_eq (tsum_congr fun u=> ?_); unfold glitter; rw [he,wide_turn,h]

lemma captain (m:ℕ)(hm:1 ≤m) (G:Gauge) (h:0<σ)(hs:0≤η)(hc:0≤C): ∃ X Y : ℝ,0≤X ∧ 0≤Y ∧ ∀ (L:Side), Threshold σ η m L→ Odd L.val → ∀ S : Cross L (Stationary.Loc G 1) (Stationary.Loc G 1), gauss S η C (4-m)→∀ T:Tile (edgeL G) (m+1), Agate T→Up T→Valed T →∀ B V, Bail (fame _) σ T B→ Bail (fame _) σ (tap T) V→ Bail (fame _) η (pearl (merit S) T) (B*(X/(L.val:ℝ)) + V*(Y*(L.val:ℝ)^3)) := by
    obtain ⟨D,E,hD,hE,H⟩:= curtain_tail h hs hc m (4-m) hm le_rfl G
    let n:ℝ:= Fintype.card (Stationary.Loc G 1)
    have hn:0≤n:=Nat.cast_nonneg _; let M:=n^(m+1)*C
    have hM:0≤M:=by unfold M; positivity
    refine ⟨M*E,M*D,mul_nonneg hM hE,mul_nonneg hM hD,fun L hw ho S ht T hT hU hz B V hV hp=>?_⟩
    let u:ℝ:=L.val;have hu:0<u:= by unfold u; positivity
    let A:=C*u⁻¹;have ha:0≤A:=by unfold A; positivity
    have hx:S.strip η A:=by simpa only [advanceC,List.length_nil,Nat.add_zero,pow_one] using ht [] (Nat.zero_le _)
    have hB:=hV.1; have hv:= hp.1
    let W:= B*(E*u⁻¹^(m+(4-m)))+D*V
    have hW:0 ≤ W := by unfold W;positivity
    let P:= u^4*(n*A)*(n^m*W); have hP:0≤P:=by unfold P;positivity
    have He a:= all_youth S T hx hs ha hV h.le hW a (fun x t=> H L hw ho S ht T hT hU hz B V hV hp x a t)
    apply (knox_frame (fame _) (pearl_agate (merit S) hT) He hP).mono
    change P ≤ _
    have Hx:u⁻¹≤1:= inv_le_one_of_one_le₀ (by unfold u;exact_mod_cast L.pos)
    have hy : u^3 * u⁻¹^(m+(4-m)) ≤ u⁻¹ := le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by positivity) Hx (show 4≤m+(4-m) by omega)) (by positivity)) (le_of_eq (by field_simp))
    have he:P=B*(M*E)*(u^3 * u⁻¹^(m+(4-m)))+ V*(M*D*u^3):=by unfold P M A W; field_simp; ring
    rw [he]; apply add_le_add_left; exact (mul_le_mul_of_nonneg_left hy (by positivity : 0≤B*(M*E))).trans_eq (by rw [mul_assoc,div_eq_mul_inv])
end YM.FormalBulk08.Chapel
