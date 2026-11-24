import YM.WilsonCoeffUV.Stable.WickAlgebra
/-! # Match Wick refund rate from polynomial supplies. -/
set_option autoImplicit false
set_option maxHeartbeats 410000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open Bank.Carp
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{V:Type*}{r h D l j i e k a m b u N M c:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A C t B x δ:ℝ}{H: Hol G}{T:SectionData F}{p:h<D}{v: Rails h k u e}{E W K U':Credit} {R S: TowerS G D}
lemma tramUp (P:ℕ→ Coil F)(p:∀ i<k, Tram F 0 (lineS (P i) 0)): Tram F 0 (lineS (steepen P k) 0):=by
    induction k with
    | zero=> rw [steepen,junior]; exact Tram.one
    | succ k ih=> rw [steepen,line_mul,Finset.Nat.antidiagonal_zero,Finset.sum_singleton]; exact (p _ (by omega)).mul (ih (fun j hj=>p _ (by omega)))
lemma lensCostU (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W V K:Credit): ∃ X:Credit,∀ L:CutsP H T p v E W K V,∃ U:Wall F,U*L.lHorizon=1∧∀ x y, ‖U x y‖≤ X.buy L.Age:=by
    obtain ⟨X,h⟩:= SeasonM e H T p E W V; refine ⟨X,fun L=>?_⟩
    let U:=bindingS L.ax L.tx T p L.N L.m L.i false; let A:= CurNames L.ax L.tx T p L.N L.m L.i false; let R:= L.vesselsC
    have hz:=L.hc.trans L.hn
    let B:=lineS U 0; let P:= forwardW L.ax L.tx T p L.N L.m L.i
    have hb: U=A⁻¹:= (ebbing L.L.L L.ha hz false).2
    have he : U*A=1:=by rw [hb]; exact Matrix.nonsing_inv_mul _ (ebbing L.L.L L.ha hz false).1
    have hg:B*P=1:=by unfold B P forwardW; simp_rw [line0]; rw [show _= A from (show CurNames L.ax L.tx T p L.N L.m L.i false=A from rfl), ← map_mul,he,map_one]
    refine ⟨identum B,?_ ,fun i j=>?_⟩
    · have hp:= (wallways L.L.L L.ha hz).2.1; have hx : Tram F 0 B:= by
          apply tramUp; intro i hi; unfold topGear; rw [maxStroke]; have hh:= leaseN L.L.L (m:=L.m+i) (N:=L.N) (L.ha.trans (Nat.le_add_right ..)) (Nat.lt_of_lt_of_le (show L.m+i<L.m+L.i from by omega) hz)
          rw [line_steed (A:=Jacob L.ax L.tx T p L.N (L.m+i)) hh, ←steed_value hh]; exact Tram.elastic hh
      change identum B * identum P=1; rw [←identT hx hp,hg,ident0]
    have hh (i j:Alma F):‖B i j‖≤ X.buy L.Age:= by
        let t: CourseS H T p e E W V:= ⟨L.L',L.windowC,by rw [L.he]; rfl⟩
        have hc:t.vols=L.vesselsC:= t.peace.symm
        have hz:‖lineS (bindingS t.vols.draws t.vols.paid T p L.N L.m L.i false) 0 i j‖≤ X.buy t.Age:= (h t _ (Nat.zero_le e) _ _).main
        rw [hc] at hz; exact hz
    unfold identum; rw [Matrix.of_apply]; split; exact hh ..
    rw [norm_zero]; exact zero_le_one.trans (X.purchase L.windowC.warm)

noncomputable def vealJ (r k:ℕ):ℝ := match k with
   | 0 => 1
   | i+1 => (i+1:ℕ)*((r+1:ℕ)*(r+2:ℕ))*vealJ (r+2) i
lemma vealPos (r k:ℕ):0< vealJ r k:=by induction k generalizing r with | zero=> rw [vealJ]; norm_num | succ k ih=> rw [vealJ]; exact mul_pos (by positivity) (ih _)
lemma cool_p (u:ℕ){P:Gen (Vote D) (YForest G)}(p:Fruit 0 1 u (P (r+2*k)) A){Z:ropes Cover (Hooks G) (Hooks G)}(h:shoulder Z B) : Fruit 0 1 u (ivern Z P k r) (vealJ r k*B^k*A):=by
   induction k generalizing r with
   | zero=> simp only [ivern,vealJ,pow_zero,one_mul]; exact p
   | succ k ih=>
       rw [ivern,Pi.smul_apply,vealJ]; let M:=(r+2); let V:=vealJ M k; let C:ℝ:= (k+1:ℕ); have hc:0<C:= by unfold C; positivity;
       have hv: r+2*(k+1)=(r+2)+2*k:=by omega
       rw [hv] at p; have hx:= (ragRain (r:=r) h.2 h.1 (ih (r:=r+2) p) zero_le_one).collectR zero_le_one
       apply Fruit.more (hx.μ C⁻¹); have ht:1≤ C:=by unfold C; exact_mod_cast Nat.le_add_left 1 k
       rw [abs_of_nonneg (by positivity)]; let U:ℝ:=((r+1:ℕ):ℝ)*((r+2:ℕ):ℝ); have hu:0≤ U:=by unfold U; positivity
       have hV:= vealPos M k; have hz:= p.C; have hB:=h.1
       apply (mul_le_mul_of_nonneg_right (show C⁻¹ ≤ C from (inv_le_one_of_one_le₀ ht).trans ht) hx.C).trans
       change C*(1/2 * B* _* _ *(V*B^k*A))≤ _
       rw [show C*(1/2 * B* _* _ * (V*B^k*A))=1/2*(C*U*V*B^(k+1)*A) from ?_]; exact mul_le_of_le_one_left (show 0≤ C*U*V*B^(k+1)*A from by unfold V; positivity) (by norm_num)
       unfold U; ring
lemma masonry (G:Gauge) (r u k:ℕ) {P:Gen (Vote D) (YForest G)}{Z: ropes Cover (Hooks G) (Hooks G)}(h:shoulder Z B)(hb:1≤ B)(p:∀j,Fruit 0 1 u (P j) A) : Fruit 0 1 u (mason Z P k r) ((∑ i∈ Finset.range (k+1),vealJ r i)*B^k*A):= by
    rw [mason, Finset.sum_apply]; simp_rw [Finset.sum_mul]; exact Fruit.sum (fun i hi=>(cool_p u (p _) h).more (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) (vealPos r i).le) (p i).C)) zero_le_one
lemma amberKiosk (H: Hol G)(T:SectionData F)(p:h<D)(v: Rails h k u e)(E W V K C:Credit): ∃ X:Credit,∀ L:CutsP H T p v E W K V, Weston L.L.L C → ∀ i: Alma F, ‖L.LensC 0 i‖≤ X.buy L.Age*L.ρ*L.fuel:=by
    obtain ⟨A,w⟩:= CutsP.moisture H T p v E W K V; let U:= C.prodC ((dome E).powC 2); let M (i:Alma F):= ∑ j∈Finset.range (k+1),vealJ (valence F i) j; let N:= ∑ i,M i; have hN i:0≤M i:= Finset.sum_nonneg fun _ _=> (vealPos ..).le; let B:=coinQ F v.sup D * N
    let X:= ((pur B).prodC (U.powC k)).prodC A
    refine ⟨X,fun L z i=>?_⟩; let R:=L.vesselsC; have ha:=L.ha; let y:=L.Age
    have hx:L.m≤L.N:=le_trans (show L.m≤ L.m+L.i by omega) (L.hc.trans L.hn); have hh:R.y L.m≤ y:=L.windowC.covers (Nat.zero_le L.i)
    have hP: L.m=L.m+0:=rfl
    obtain ⟨he,hv⟩:= tolling R C ha (le_refl L.m) hx hx (z.hcap L.m ha); have ha':= R.depth _ ha
    let Z:=L.springP 0; let A':= A.buy y*L.ρ*L.fuel; have hp j : Fruit 0 1 u (Z.2 0 j) A':= (w L 0 (Nat.zero_le e) 0 (Nat.zero_le L.i) j).wax
    have hk:= masonry G (valence F i) u k he (U.purchase ha') hp
    apply (p_val0 v.sup (Y:=(paveS L.ax L.m L.N k (Z.2 0) (valence F i))) hk i (valence_cap ..)).trans -- name P
    have hb:=coinSoar F v.sup D; have hm:M i≤ N:= Finset.single_le_sum (fun i _=>hN i) (Finset.mem_univ i); have hy:0≤R.cash U L.m:= zero_le_one.trans (U.purchase ha')
    rw [show _ *((_ *_)*_)= (coinQ F v.sup D*M i)*(R.cash U L.m)^k*A' from by unfold A' M; ring]; apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul ((mul_le_mul_of_nonneg_left hm hb).trans (pure_goal B y)) (pow_le_pow_left₀ hy (U.elder ha' hh) _) (pow_nonneg hy _) (zero_le_one.trans ((pur B).purchase L.windowC.warm))) (hp 0).C); exact le_of_eq (by unfold A' X y; rw [Credit.products ((pur B).prodC (U.powC k)) A,Credit.products (pur B),Credit.power U]; ring)

theorem fan_jet (H:Hol G)(T:SectionData F)(p:h<D)(v: Rails h k u e)(E W V K B:Credit): ∃ C:Credit,∀ L:CutsP H T p v E W K V, Weston L.L.L B→ ∀ i:Alma F,
    ‖(Wray L.ax L.tx T p L.N L.ceilC *ᵥ fun i=> coeff 0 (L.tileP i)) i - wickT L.ax L.ceilC L.N k F L.pt.2 i‖ ≤ C.buy L.Age* L.ρ* L.fuel:=by
    obtain ⟨X,x⟩:= lensCostU H T p v E W V K; obtain ⟨U,q⟩:= amberKiosk H T p v E W V K B; let V: Credit:= pur (Fintype.card (Alma F):ℝ); refine ⟨(V.prodC X).prodC U,fun L W i=>?_⟩; rw [norm_sub_rev,← L.topViz]
    obtain ⟨S,e,h⟩:= x L; rw [show L.LensC L.i= S*ᵥ (L.LensC 0) from Eq.symm (by rw [L.lensBridge, Matrix.mulVec_mulVec,e, Matrix.one_mulVec])]; unfold Matrix.mulVec dotProduct; let a:=L.Age; have hx:= L.windowC.warm
    let A:=X.buy a; have ha:0≤ A:=zero_le_one.trans (X.purchase hx); let B:=U.buy a*L.ρ*L.fuel; let C:=A*B; have hB:0≤ B:=le_trans (norm_nonneg _) (q L W i)
    apply le_trans (norm_sum_le ..); refine (Finset.sum_le_sum (fun j _=> (show ‖S i j*L.LensC 0 j‖ ≤ C from (by rw [norm_mul]; exact mul_le_mul (h i j) (q L W j) (norm_nonneg _) ha)))).trans ?_
    rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Credit.products,Credit.products]; exact (mul_le_mul_of_nonneg_right (pure_goal _ a) (show 0≤C from mul_nonneg ha hB)).trans_eq (by unfold C A V B a; ring)
end YM.WilsonCoeffUV.Shard
