import YM.FormalBulk08.Trellis.Low
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Trellis
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {I : Type*}[Fintype I][DecidableEq I] {X:Type}{s:X→ℕ}{τ:Time X}{E e:ℕ}
variable {δ:X→ℝ}{μ:X→ℕ→ℝ}
-- numeric in window Z. any step contribution bounded past μ only, dust μ identical. permits variable subintervals
lemma echelons {f:X→ℕ→ℝ}{u:X→ℕ→ℝ}(hp:∀ i: Dove.Walk s, |f i.z (i.i+1)| ≤ |f i.z i.i| + |u i.z i.i|)(h: Soft (tcash τ s) (fun i=>u i.z i.i))(hs:Soft τ (fun i=>(s i:ℝ)))(he:Soft τ (fun i=> f i 0)) : Soft (tbook τ s) (fun i=> f i.z i.i):= by
    have H := sum_soft (f:=fun i j=> |u i j|) h.radius hs
    have hh (j:X)(n)(h:n≤ s j): |f j n| ≤ |f j 0| +∑ i∈Finset.range n,|u j i|:= by
       induction n with
       | zero=> simp
       | succ n ih=> rw [Finset.sum_range_succ,←add_assoc]; exact (hp (⟨j,n,h⟩:Walk s)).trans (add_le_add_left (ih (by omega)) (abs _))
    exact ((he.radius.reach Lengths.z).plus H).below (fun i=>(hh i.z i.i i.endD).trans (le_abs_self _))
lemma placid {f:X→ℕ→ℝ}{u:X→ℕ→ℝ}(hp:∀ i:Dove.Walk s, |f i.z (i.i+1)| ≤ |f i.z i.i| + |u i.z i.i|)(h:Faint (tcash τ s) (fun i=>δ i.z) (fun i=>u i.z i.i))(hs:Soft τ (fun i=>(s i:ℝ)))(he:Faint τ δ (fun i=>f i 0))(hx:∀ i,0≤δ i): Faint (tbook τ s) (fun i=>δ i.z) (fun i=> f i.z i.i):= by
   have H:= sum_faint (f:=fun i j=> |u i j|) (h.lower (fun i=>by rw [abs_abs])) hs hx
   have hh (j:X)(n)(h:n≤ s j): |f j n| ≤ |f j 0| +∑ i∈Finset.range n,|u j i|:= by
       induction n with
       | zero=> simp
       | succ n ih=> rw [Finset.sum_range_succ,←add_assoc];exact (hp (⟨j,n,h⟩:Dove.Walk s)).trans (add_le_add_left (ih (by omega)) (abs _))
   exact (((he.lower (g:=fun i=> |f i 0|) (fun _=> le_of_eq (abs_abs _))).link Lengths.z).plus H).lower (fun i=> (hh i.z i.i i.endD).trans (le_abs_self _))
lemma wheelR {f g u v:X→ℕ→ℝ}(hp:∀ i:Dove.Walk s,f i.z (i.i+1)= μ i.z i.i*f i.z i.i+u i.z i.i)(he:∀ i: Dove.Walk s,g i.z (i.i+1)=μ i.z i.i*g i.z i.i+v i.z i.i)(hm:∀ i:Dove.Walk s, |μ i.z i.i|≤1)(hx: ∀ i,0≤δ i)(hs:Soft τ (fun i=>(s i:ℝ))) (h:Pact (tcash τ s) (fun i=>δ i.z) (fun i=>u i.z i.i) (fun i=>v i.z i.i))(H:Pact τ δ (fun i=>f i 0) (fun i=>g i 0)): Pact (tbook τ s) (fun i=>δ i.z) (fun i=>f i.z i.i) (fun i=> g i.z i.i) := by
    have hT (f g:X→ℕ→ℝ)(h:∀ i:Dove.Walk s,f i.z (i.i+1)=μ i.z i.i*f i.z i.i+g i.z i.i):∀ i:Dove.Walk s,|f i.z (i.i+1)|≤ |f i.z i.i| + |g i.z i.i|:= fun i=> by rw [h i];apply (abs_add_le ..).trans;rw [abs_mul]; exact add_le_add_left (mul_le_of_le_one_left (abs_nonneg _) (hm i)) _
    exact ⟨echelons (hT _ _ hp) h.left hs H.left,echelons (hT _ _ he) h.right hs H.right,placid (f:=f-g) (hT (f-g) (u-v) (fun i=>by simp only [Pi.sub_apply, hp i, he i];ring)) h.blur hs H.blur hx⟩

-- matrix steps in common variable.
def propels (Q:ℕ→Pennants I) (U:Pennants I) : ℕ→Pennants I
    | 0=>U
    | i+1=>Q i*propels Q U i
variable {w r: I→ℕ}{Q Z:X→ℕ→ Pennants I}{T U:X→Pennants I}{F:X→ℕ→I→ℝ}
lemma riders (h:∀ i:Dove.Walk s, Found w r (Q i.z i.i) (F i.z i.i))(he:∀ i:Dove.Walk s,Found w r (Z i.z i.i) (F i.z i.i))(ht:∀ i:Dove.Walk s,∀ j, F i.z i.i j≤1)(hp:∀ i j,Priced (tcash τ s) (fun i=>δ i.z) (fun z=> Q z.z z.i i j) (fun z=> Z z.z z.i i j) E)(hx:∀ i j, Priced τ δ (fun x=>T x i j) (fun x=> U x i j) E)(hy:Soft τ (fun i=>(s i:ℝ)))(h':∀ i,0≤δ i):
    ∀ i j, Priced (tbook τ s) (fun i=>δ i.z) (fun z=>propels (Q z.z) (T z.z) z.i i j) (fun z=> propels (Z z.z) (U z.z) z.i i j) E:= by
    intro i j n hn
    -- priority inc from S row→nonzero col moves LESS? priority smaller for lower slots. Here i row lower slots; k input larger slots, priority greater; induction reverse priority
    induction n using Nat.strong_induction_on generalizing i with
    | _ n ih=>
       let π:= Roof.priority w r; let B:=∑ i,π i;have hb i:π i≤ B:= Finset.single_le_sum (f:=π) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
       generalize hv:B-π i =k
       induction k using Nat.strong_induction_on generalizing i with
       | _ k hk=>
         let W x:=propels (Q x) (T x);let L x:=propels (Z x) (U x); let R:= (Finset.univ:Finset I) ×ˢ Finset.antidiagonal n;let t: I × (ℕ×ℕ):=(i,0,n);let S:= R.erase t
         let D (P:Pennants I) (M:Pennants I)(i' : I × (ℕ × ℕ)):=coeff i'.2.1 (P i i'.1)*coeff i'.2.2 (M i'.1 j)
         let z(P M:Pennants I):=∑ i'∈S,D P M i'
         have hp'(v:I→ℝ)(P M:Pennants I)(h:Found w r P v): coeff n ((P*M) i j) = v i * coeff n (M i j)+z P M:= by
             rw [subpays,←Finset.sum_product'];change (∑ a∈R,D P M a)=_; unfold z S; rw [← Finset.add_sum_erase R (D P M) (show t∈R from Finset.mem_product.mpr ⟨Finset.mem_univ _,by simp [t]⟩)];exact congr_arg (· + _) (congr_arg (fun c=>c * coeff n (M i j)) (h.due i))
         refine wheelR (f:=fun x n' => coeff n (W x n' i j)) (g:=fun x n' => coeff n (L x n' i j)) (μ:=fun x n'=> F x n' i) (u:=fun x a=> z (Q x a) (W x a)) (v:=fun x a=>z (Z x a) (L x a)) (fun i=>hp' _ _ _ (h i)) (fun i=>hp' _ _ _ (he i)) (fun y=>by rw [abs_of_pos ((h y).scale _)];exact ht y i) h' hy ?_ (hx i j n hn)
         unfold z;apply pact_sums S (f:=fun i' (y:Dove.Walk s)=>D (Q y.z y.i) (W y.z y.i) i') (g:=fun i' (y:Dove.Walk s)=>D (Z y.z y.i) (L y.z y.i) i')
         rintro ⟨u,a,b⟩ ha; obtain ⟨hs,hy⟩:=Finset.mem_erase.mp ha; have hz:a+b=n:=Finset.mem_antidiagonal.mp (Finset.mem_product.mp hy).2
         by_cases hV:b<n
         · exact (hp i u a (by omega)).times ((ih b hV u (by omega)).link stubW)
         have he' : b=n:=by omega
         have hy:a=0:=by omega
         subst a b; by_cases hu:π i <π u
         · have hv: B-π u < k:= by have hp:=hb u; omega
           exact (hp i u 0 (Nat.zero_le _)).times ((hk (B-π u) hv u rfl).link stubW)
         have hh : i≠u:= fun hi=>hs (Prod.ext hi.symm rfl)
         have hF (x:Dove.Walk s) : D (Q x.z x.i) (W x.z x.i) (u,(0,n))=0:= mul_eq_zero.mpr (Or.inl (show coeff 0 _=0 from Classical.byContradiction fun p=>hu (promotes ((h x).min i u p hh))))
         have he (x:Dove.Walk s): D (Z x.z x.i) (L x.z x.i) (u,(0,n))=0:= mul_eq_zero.mpr (Or.inl (show coeff 0 _=0 from Classical.byContradiction fun p=> hu (promotes ((he x).min i u p hh))))
         simp_rw [hF,he]; exact Pact.coin ..
end YM.FormalBulk08.Trellis
