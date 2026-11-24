import YM.Frontier6.Normal.Sums

/-! Over-summation is an extension. Local test domain. In subsequent rules
absolute convergence must be checked also on the general joint tests; this
module doesn't assume any positivity. Full local cost will also provide
continuity separately. -/
set_option linter.unusedSectionVars false
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Normal
open Function Filter Set MeasureTheory Metric
open scoped Topology ContDiff BigOperators Classical
variable {X Y:Type*}[NormedAddCommGroup X][InnerProductSpace ℝ X][FiniteDimensional ℝ X][NormedAddCommGroup Y]
def Void (f:Full X):Prop:= (0:X)∉tsupport f
variable {f g:Full X}
lemma void_zero: Void (0:Full X):=by simp [Void,FunLike.coe_zero]
lemma fits_zero (s:ℝ): Fits s (0:Full X):=by simp [Fits,FunLike.coe_zero]
omit [FiniteDimensional ℝ X] in
lemma Void.add (h:Void f)(e:Void g):Void (f+g):=fun he=> ((tsupport_add f g) he).elim h e
omit [FiniteDimensional ℝ X] in
lemma Void.sub (h:Void f)(e:Void g):Void (f-g):=fun he=> ((tsupport_sub f g) he).elim h e
lemma Void.vanishes (h:Void f)(j:ℕ): iteratedFDeriv ℝ j f 0=0:= image_eq_zero_of_notMem_tsupport (fun e=> h (tsupport_iteratedFDeriv_subset j e))
lemma Void.smul (h:Void f)(z:ℂ): Void (z • f):= by
   intro hc; apply h
   have he:support (z • f)⊆support f:=fun x hx=> by_contra fun he=> hx (by have hu:f x=0:=notMem_support.mp he; simp [hu]) -- indent
   exact closure_mono he hc
lemma void_left (f:Full X)(h:Void f)(s:ℝ)(m:ℕ): leftOut s m f=f:= by rw [left_as,portion_zero s m (fun i _=>h.vanishes i),sub_zero]
lemma void_piece {s:ℝ}(hs:0<s)(f:Full X):Void (Piece s f):=fun h=> by have he:= (show s/2≤ ‖(0:X)‖ from (piece_ring hs f h).1); rw [norm_zero] at he; linarith
lemma sums_void_cut {f:Full X}(h:Void f): ∀ᶠ i:ℕ in atTop, join (shrink X (pitch i)) f=0:=by
   obtain ⟨r,hr,he⟩:= Metric.nhds_basis_closedBall.mem_iff.mp (mem_nhds_iff.mpr ⟨(tsupport f)ᶜ, Subset.rfl, isOpen_compl_iff.mpr (isClosed_tsupport _), (show 0 ∈ (tsupport f)ᶜ from h)⟩) -- syntax
   have ht:Tendsto (fun i=>2*pitch i) atTop (𝓝 0):=by simpa only [mul_zero] using pitch_down.const_mul (2:ℝ)
   filter_upwards [ht.eventually (ge_mem_nhds hr)] with i hi
   ext1 x; by_contra hw
   have hp:x∈tsupport (join (shrink X (pitch i)) f):= subset_closure hw
   exact he (show x∈closedBall (0:X) r from closedBall_subset_closedBall hi (shrink_fits (pitches i) (join_left (shrink X (pitch i)) f hp))) (join_right (shrink X (pitch i)) f hp)

lemma telescope (f:Full X)(i:ℕ): Piece (pitch i) f=join (shrink X (pitch i)) f-join (shrink X (pitch (i+1))) f:=by
   ext1 x; rw [pitch_even]; change ( (shrink X (pitch i) x) - (shrink X (pitch i / 2) x))* f x= (_ * _) - _ * _; ring
lemma telescopes (f:Full X)(h:Fits 1 f)(n:ℕ) : ∑ i∈ Finset.range n, Piece (pitch i) f=f-join (shrink X (pitch n)) f:=by
   induction n with
   | zero=>
     have he: join (shrink X (pitch 0)) f=f:=by
        ext1 x
        by_cases hx:‖x‖ ≤ 1
        · rw [join_apply,shrink_home (pitches 0) _ ((by simpa [pitch] using hx):‖x‖ ≤ pitch 0),one_mul]
        simp [h.out x (lt_of_not_ge hx)]
     rw [he]; simp
   | succ n ih=> rw [Finset.sum_range_succ, ih,telescope]; abel

variable [NormedSpace ℂ Y]
/-- No topology requirement here; algebraic test-law specifically on
cross-collision supports. Prices separate. -/
structure Law (F:Full X → Y)(r:ℝ):Prop where
 zero:F 0=0
 add {f g:Full X} : Fits r f → Fits r g→F (f+g)=F f+F g
 scalar (c:ℂ){f:Full X}: Fits r f→ F (c • f)=c • F f

structure Sect (F:Full X → Y)(r:ℝ):Prop where
 zero:F 0=0
 add {f g:Full X}: Fits r f → Void f → Fits r g → Void g → F (f+g)=F f+F g
 scalar (c:ℂ){f:Full X}: Fits r f→ Void f→ F (c • f)=c • F f

variable {F:Full X→Y}{r:ℝ} {P Q:ℝ}
lemma Sect.sub {H H':Full X→ Y}(h:Sect H r)(g:Sect H' r): Sect (H-H') r:=by
   refine ⟨sub_eq_zero.mpr (h.zero.trans g.zero.symm),fun {u v} hu hz hv hh=>?_,fun c {u} hu hv=>?_⟩
   · simp only [Pi.sub_apply,h.add hu hz hv hh,g.add hu hz hv hh]; abel
   simp only [Pi.sub_apply,h.scalar c hu hv,g.scalar c hu hv,smul_sub]
lemma Sect.into {Z:Type*}[NormedAddCommGroup Z][NormedSpace ℂ Z](h:Sect F r)(L:Y→L[ℂ] Z):Sect (L ∘ F) r:=
    ⟨by simp [h.zero],fun {u v} hu hz hv hh=> by simp only [Function.comp_apply,h.add hu hz hv hh,map_add],fun c {u} hu hv=> by simp only [Function.comp_apply,h.scalar c hu hv,map_smul]⟩
lemma Law.down (h:Law F r){s:ℝ}(e:s≤r):Law F s:=⟨h.zero,fun {u v} hu hv=> h.add (hu.up e) (hv.up e),fun c {u} hu=> h.scalar c (hu.up e)⟩
lemma Sect.down (h:Sect F r){s:ℝ}(e:s≤r):Sect F s:=⟨h.zero,fun {u v} hu hv he hh =>h.add (hu.up e) hv (he.up e) hh,fun c {u} hu hv=>h.scalar c (hu.up e) hv⟩
lemma Sect.sum {I:Type*}(h:Sect F r) (f:I→Full X)(hf:∀ i, Fits r (f i))(hx:∀ i, Void (f i))(s:Finset I): F (∑ i∈s,f i)=∑ i∈s,F (f i):=by
   have hl(s:Finset I):Fits r (∑ i∈s,f i) ∧ Void (∑ i∈s,f i):=by
      induction s using Finset.induction_on with
      | empty=>simpa using And.intro (fits_zero (X:=X) r) (void_zero (X:=X))
      | insert i s hi ih=> rw [Finset.sum_insert hi]; exact ⟨(hf i).add ih.1,(hx i).add ih.2⟩
   induction s using Finset.induction_on with
   | empty=>simpa using h.zero
   | insert i s hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi,h.add (hf i) (hx i) (hl s).1 (hl s).2,ih]
lemma Sect.recovers (h:Sect F r)(hr:r≤1) (he:Fits r f)(hf:Void f): over F f=F f:=by
   obtain ⟨n,H⟩:=eventually_atTop.mp (sums_void_cut hf)
   unfold over; rw [tsum_eq_sum (s:=Finset.range n) (fun i hi=> ?_), ← show F (∑ i∈Finset.range n,Piece (pitch i) f)=∑ i∈Finset.range n, based F f i from h.sum (fun i=>Piece (pitch i) f) (fun i=> piece_fits he) (fun i=> void_piece (pitches i) f) _,telescopes f (he.up hr),H n le_rfl,sub_zero]
   unfold based; have hp: n≤ i:= by simpa using hi
   rw [telescope,H i hp,H (i+1) (by omega),sub_self,h.zero] -- indent

variable [CompleteSpace Y]
lemma Sect.sums_as (h:Sect F r)(he:Fits r f)(hg:Fits r g)(hf: Summable (based F f)) (hh:Summable (based F g)) : over F (f+g)=over F f+over F g:=by
   unfold over
   have hp(i): based F (f+g) i=based F f i+based F g i:=by unfold based; rw [map_add]; exact h.add (piece_fits he) (void_piece (pitches i) _) (piece_fits hg) (void_piece (pitches i) _)
   rw [show based F (f+g)= based F f+based F g from funext hp]; exact hf.tsum_add hh
lemma Sect.sums_scaled (h:Sect F r)(he:Fits r f)(hf: Summable (based F f))(z:ℂ): over F (z • f)= z • over F f:=by
   unfold over; have hp(i): based F (z • f) i=z • based F f i:=by unfold based; rw [map_smul]; exact h.scalar z (piece_fits he) (void_piece (pitches i) _)
   rw [show based F (z • f)= z • based F f from funext hp]; exact hf.tsum_const_smul z -- check name
lemma Sect.sums_zero (h:Sect F r): over F 0=0:=by simp [over,based,h.zero]
lemma Sect.residue_sum {σ:ℝ}{j:ℕ}(h:Sect F r)(he:r≤1)(hp:Fits r f)(hv:0<σ)(hF:RingPrices j σ r F P): Summable (based F f):= by
   obtain ⟨A,hA⟩:=exists_charge j f 1 zero_le_one
   exact ((normal_residue_prices (Y:=Y) (X:=X) j σ 1 hv le_rfl).choose_spec.2 r P 1 A F h.zero hF zero_lt_one f hp (by rw [one_mul]; exact hp.up he) hA).sums
lemma Sect.rule_residue {σ:ℝ}{j:ℕ}(h:Sect F r)(he:r≤1)(hv:0<σ)(hF:RingPrices j σ r F P): Law (over F) r:= ⟨h.sums_zero,fun {u v} hu ht=> h.sums_as hu ht (h.residue_sum he hu hv hF) (h.residue_sum he ht hv hF),fun c {u} hu=> h.sums_scaled hu (h.residue_sum he hu hv hF) c⟩
omit [NormedSpace ℂ Y] in
lemma portion_sum {σ s:ℝ}{m j:ℕ} (he:2*s≤r)(hs:0<s)(hv:0<σ+(m:ℝ)+1)(hσ:σ+(m:ℝ)<0)(hF:RingPrices j σ r F P)(hp:Fits r f) : Summable (based F (leftOut s m f)):=by
   obtain ⟨A,hA⟩:=exists_charge (j+m+1) f s hs.le
   have hz:r/s≥1:=(one_le_div hs).2 (by linarith)
   exact ((normal_portion_prices (Y:=Y) (X:=X) j m σ (r/s) hz hv hσ).choose_spec.2 r P s A s F hF hs hs he (by rw [div_mul_cancel₀ _ hs.ne']; linarith only [hs,he]) f hp (by rw [div_mul_cancel₀ _ hs.ne']; exact hp) hA).sums
lemma Sect.rule_portion {σ s:ℝ}{m j:ℕ}(h:Sect F r)(he:2*s≤r)(hs:0<s)(hv:0<σ+(m:ℝ)+1)(hσ:σ+(m:ℝ)<0)(hF:RingPrices j σ r F P): Law (fun f=>over F (leftOut s m f)) r:=by
   refine ⟨by rw [map_zero]; exact h.sums_zero,fun {u v} hp hq=>?_,fun c {u} hp=>?_⟩
   · rw [map_add]; exact h.sums_as (left_fits hs m hp he) (left_fits hs m hq he) (portion_sum he hs hv hσ hF hp) (portion_sum he hs hv hσ hF hq)
   rw [map_smul]; exact h.sums_scaled (left_fits hs m hp he) (portion_sum he hs hv hσ hF hp) c
lemma Law.finAdd (h:Law F r)(L:Y→L[ℂ] Y): Law (L ∘ F) r:=⟨by simp [h.zero],fun {u v} p q=>by simp only [Function.comp_apply,h.add p q,map_add],fun c {u} p=>by simp only [Function.comp_apply,h.scalar c p,map_smul]⟩
end YM.Frontier6.Normal
