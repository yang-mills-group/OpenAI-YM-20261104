import YM.RGGapR2.Cargo
/-! Initialization of full conditional discrepancy by subtracting ONLY
  the localized singleton exponential (it includes the unit) as an
  actual multiplicative source within the same marked integral. We
  retain the preexisting multiple terms H,K, assign all forced addresses
  and the complementary wide regular occurrences in non-quiet modes
  with explicit price. No secondary vacuum approximation or use of a
  ratio on a flag set assumed typical. This is a new error currency for
  the rough transfer only (the tight singleton recurrence before this
  subtraction still uses its own derivative/forced-divided prices).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGGapR2.Harrier
open Function Finset Filter Set Lattice Wilson RG Source MeasureTheory Ac Push Local Extra.Histories PhysicalNext.Repeat Lotus Merge Merge.Palette Marker Overlay
open MergeProof MergeProof.Menu MergeProof.Accent Extra.Multi GridApprox.Nil Extra.Trajectories Planned.GuardedAtom
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
set_option quotPrecheck false
set_option maxHeartbeats 2400000
set_option maxRecDepth 7000

variable {V : Type}[DecidableEq V][Fintype V]{B:Census V}{G:Gauge}{n:Side}
variable {R:Rep G n}{o:V→Site n}{μ:ℕ}{d a b x t:ℝ}{w:V→ℝ}
local notation "η"=> (R).p
local notation "L!"=> (R).activities
section
local notation "Ξ"=> V×ℕ
variable {g: V×ℕ → Config G n→ℂ}
def stamps (g: V×ℕ → Config G n→ℂ)(i:V×ℕ)(U:Config G n):Poly B:=Poly.send (B.fire i.1) (g i U)
variable {X:V×ℕ→ Support n}
lemma ready (hw:∀ i,0<w i)(h:Occupancy o μ)(ha:0 ≤ a){f:V×ℕ→ℝ}
    (hy:∀ i U,‖g i U‖≤f i)(ht:∀ i,SumBudget (fun j:ℕ=> Real.exp ((d+1)*coverNumber (R.p.B) (X (i,j))) *(w i*f (i,j))) a)(ho:∀ i,0<f i→ o i.1∈X i) :
     Towed (B:=B) w X (stamps g) (R.p.B) d (μ*siteFactor (R.p.B)*a):=by
       classical
       let z (i:V×ℕ) := w i.1*f i; have hf(i):0 ≤ f i:=(norm_nonneg _).trans (hy i 1)
       have hz(i):0 ≤ z i:= mul_nonneg (hw i.1).le (hf i)
       have he(i):Summable fun j:ℕ=> z (i,j) :=by
         by_cases hh:0 ≤ d+1; swap
         · have hfinite : ∀ X:Support n, 0<Real.exp ((d+1)*coverNumber (R.p.B) X):= fun _=>Real.exp_pos _
           let h(Z:Support n):= (Real.exp ((d+1)*coverNumber (R.p.B) Z))⁻¹; obtain ⟨Z,H,hZ⟩:= Finset.exists_max_image univ h Finset.univ_nonempty
           refine ((ht i|>.2.1).mul_left (h Z)).of_nonneg_of_le (fun j=>hz _) (fun j=>le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right (hZ (X (i,j)) (mem_univ _)) (show 0≤ Real.exp _ * (w i*f _) from (ht i|>.1 _))))
           dsimp only [z,h]; rw [inv_mul_cancel_left₀ (hfinite _|>.ne')]
         refine (ht i|>.2.1).of_nonneg_of_le (fun j=>hz _) (fun j=> le_mul_of_one_le_left (hz _) (Real.one_le_exp (mul_nonneg hh (Nat.cast_nonneg _))))
       have hZ:Summable z:=(summable_prod_of_nonneg hz).2 ⟨he,Summable.of_finite⟩
       let m(i:V×ℕ):=(B.fire i.1).val
       refine ⟨z,hZ,root_hit (X:=X) (mode:=m) h hz ha (fun i hi=>⟨i.1,mem_singleton_self _,ho i (pos_of_mul_pos_right hi (hw _).le)⟩) ?_,fun j=>?_⟩
       · intro i
         let p(i':V×ℕ):=if i∈m i' then (Real.exp ((d+1)*coverNumber (R.p.B) (X i')))*(z i') else 0
         have hp (j):Summable fun k:ℕ=>p (j,k) :=by by_cases hj:i=j <;> simp only [p,m,Prod.fst,Census.fire,Finset.mem_singleton,hj,↓reduceIte,z];exact (ht j|>.2.1);exact summable_zero
         have h0(q):0≤p q:=by unfold p;split;exact mul_nonneg (Real.exp_pos _).le (hz _); rfl
         have ht':Summable p:= (summable_prod_of_nonneg h0).2 ⟨hp,Summable.of_finite⟩
         suffices hmain: SumBudget p a by
            convert! hmain using 1
            funext x
            unfold p
            split_ifs <;> rfl
         refine ⟨h0,ht',le_trans ?_ (ht i|>.2.2)⟩
         rw [ht'.tsum_prod,tsum_fintype, Finset.sum_eq_single i]
         · simp [p,m,Census.fire,z]
         · intro j _ hj; unfold p; simp [m,Census.fire,hj.symm]
         simp
       simpa only [Poly.solo_toll] using! satin (g j) (B.fire _) _ (hf _) (w:=w) (hy j)

variable (B) {J I:Type}[Finite J]{X:J → Support n} {k:I→J}
lemma stamp_silent {Z:I→ Config G n→Poly B} (h:∀ i U,(Z i U).part B.quiet=0)(hz:∀ U,Summable fun i:I=> Z i U) (j:J)(U:Config G n): (tally k Z j U).part B.quiet=0:=by
   rw [tally,Poly.share]; exact (tsum_congr (fun q=> h _ _)).trans tsum_zero
   exact (hz _).comp_injective Subtype.val_injective
variable {Z:I→ Config G n→Poly B}
lemma Towed.plus' {Z':I → Config G n →Poly B}{P:I→Support n}(h1:Towed w P Z R.p.B d a)(h2:Towed w P Z' R.p.B d b)(hw0:∀ i,0<w i):Towed (B:=B) w P (Z+Z') R.p.B d (a+b):=by -- syntactic R.p.B arrows spaces
     obtain ⟨u,hu,hp,hU⟩:=h1; obtain ⟨v,hv,hq,hV⟩:=h2
     refine ⟨fun i=> u i+v i,hu.add hv,fun i=> ?_,fun i=>?_⟩
     · convert! Extra.Multi.Budget.plus (hp i) (hq i) using 1; ext j; dsimp only; split_ifs <;> ring
     obtain ⟨x,hx,hT,hX⟩:=hU i;obtain ⟨y,hy,hτ,hY⟩:=hV i
     refine ⟨fun l=> x l+y l,fun j=>add_nonneg (hx _) (hy _),fun U p=>?_,?_⟩
     · change ‖(Z i U+Z' i U).part p‖ ≤ _; rw [Poly.part_plus]; exact (norm_add_le ..).trans (add_le_add (hT ..) (hτ ..))
     unfold wordsPrice; dsimp only; simp_rw [mul_add,Finset.sum_add_distrib]; exact add_le_add hX hY
variable {P:Type}
lemma Borne.plusB {Z:P → Config G n→Poly B}(i:P) {Z':P → Config G n →Poly B}(Q:Support n)(h1:Borne o Q (Z i) t) (h2:Borne o Q (Z' i) t): Borne o Q ((Z+Z') i) t:=by
     constructor
     · exact fun U V hX hF=> congr_arg₂ (·+·) (h1.home U V hX hF) (h2.home U V hX hF)
     · exact fun g U=> congr_arg₂ (·+·) (h1.turns g U) (h2.turns g U)
     · exact fun p=> (h1.me p).add (h2.me p)
     intro U p hp; change ((Z i U).part p+(Z' i U).part p)=0; rw [h1.scope U p hp,h2.scope U p hp,zero_add]
-- P unknown var
private lemma zeros [k:Fintype J] (Y:J→ Config G n→Poly B)(hZ:∀ i U,(Y i U).part B.quiet=0)(U:Config G n):(∑ i,Y i U).part B.quiet=0:=by rw [Poly.part_sum]; simp only [hZ,Finset.sum_const_zero]
local notation "M!" f => Mach B f
variable {V₀: V→ Config G n→ℂ}{g₀:V→Box n→ Config G n→ℂ}{F':Config G n→Poly B}
    (E:Support n→ Config G n→Poly B)(K:Box n→ Config G n→Poly B)(Y:V→ Config G n→ℂ)
def reducedAt (F:Config G n→Poly B)(l:V→ Config G n→ℂ):Config G n →Poly B:= fun U=>F U* Poly.pass (-Mach B (fun j=>l j U))
lemma resume {P:Support n} (h:Served R V₀ g₀ F' o w d a)(hE:∀ i,Burns o i (E i) R.p.threshold)(hK:∀ i,Flow o i (K i) R.p.threshold ∧ ∀ U,(K i U).part B.quiet=0)(hd:Towed w id E R.p.B d b)(hv:Towed w Prod.fst K R.p.B d b)
    (he:∀ U, Mach B (fun i=>V₀ i U-Y i U)=∑ i,E i U)(hx:∀ i U,Mach B (fun j=>g₀ j i U)=K i U)(hw0:∀ i,0<w i): YM.RGGapR2.Rough.Freight R B (reducedAt B F' Y) o w d (a+b):=by
      obtain ⟨H,L,hH,h1,h2,hF⟩:=h; have hp(i:Box n)(u:Config G n):bar R.activities B u i+Mach B (fun j=>g₀ j i u) + L i u=bar R.activities B u i+ (L i u + K i u) :=by rw [hx i u]; ac_rfl
      refine ⟨H+E,L+K,⟨fun i=> ⟨Borne.plusB B i i (hH.exp i|>.1.toBorne) (hE i).toBorne,fun u hi=>?_ , fun U=>by change (H i U+E i U).part (Census.quiet _)=0; rw [Poly.part_plus,(hH.exp i).1.sil,(hE i).sil,zero_add]⟩,fun i=>⟨⟨Borne.plusB B i i.1 (hH.flag i|>.1.toBorne) (hK i|>.1.toBorne), fun U hi=>?_⟩,fun U=>?_⟩⟩,Towed.plus' B h1 hd hw0,Towed.plus' B h2 hv hw0,?_⟩ -- adjust
      · rcases eq_or_ne (H i u) 0 with hh|hn
        · exact ((hE i).permits u) (by change H i u+E i u≠0 at hi;rwa [hh,zero_add] at hi)
        exact ((hH.exp i).1.permits u hn)
      · rcases eq_or_ne (L i U) 0 with hh|hn
        · exact ((hK i).1.permits U) (by change L i U+K i U≠0 at hi;rwa [hh,zero_add] at hi)
        exact ((hH.flag i).1.permits U hn)
      · change (L i U+K i U).part B.quiet=0; rw [Poly.part_plus,hop B _ ((hH.flag i).2 _),(hK i|>.2 U),zero_add]
      funext U
      let m(f:V→ Config G n→ℂ):= Mach B (fun i=>f i U)
      have hm: m V₀ + ∑ i,H i U+(-m Y)=∑ i,(H+E) i U:=by
          change _ = ∑ i, (H i U+E i U); rw [Finset.sum_add_distrib]
          have ht: m V₀ - m Y=Mach B (fun i=> V₀ i U - Y i U):=by
             unfold m Mach; rw [← Finset.sum_sub_distrib]; congr 1; ext i :1; rw [show (Poly.send (B.fire i) (V₀ i U)-Poly.send (B.fire i) (Y i U))=Poly.send (B.fire i) (V₀ i U-Y i U) by ext p;rw [part_sub]; simp [Poly.part_send]; split <;> simp]
          rw [← he,← ht]; abel
      unfold reducedAt; rw [hF]; unfold play restore
      simp_rw [hp]
      change (↑(Real.exp _):ℂ) • (Poly.pass (m V₀+∑ i,H i U) * _) * Poly.pass (-m Y) = (↑(Real.exp _):ℂ) • (Poly.pass (∑ i,(H+E) i U) * _)
      have ht:(m V₀ + ∑ i,H i U).part B.quiet=0:=by rw [Poly.part_plus,mute,zeros,add_zero]; exact fun i U=>(hH.exp i|>.1.sil _)
      have hy:(-m Y).part B.quiet=0:=by change -(m Y).part B.quiet=0; rw [mute,neg_zero]
      rw [smul_mul_assoc,← hm,pass_add ht hy]; simp only [exclaim, Pi.add_apply]; exact congr_arg ((↑(Real.exp ((R).exponent U)):ℂ) • ·) (mul_right_comm ..)
end
