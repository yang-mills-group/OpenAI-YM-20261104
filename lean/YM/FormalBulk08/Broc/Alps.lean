import YM.FormalBulk08.Broc.Iced

/-! Read an ALL-grade Pot from a path. For these operations on
precisely the same mesh, any stronger head needs purchase before L;
none iterates unchanged in this representation. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Broc
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North Cork City
open Precision
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{s:Signed}{r t e E:ℕ}{A σ:ℝ}
lemma uncut_coast (p:ℕ→Atom G r)(U:Config G n)(b:Site n): uncut p (pull 1 b U)=uncut p U:= by
   have he i x: (p i).unmasked (pull 1 b U) x= (p i).unmasked U (x+b):= by
       have hv: expandAt x (pull 1 b U)=expandAt (x+b) U := by funext;rw [pull_one]; simp [expandAt, Lattice.translate,add_assoc]
       simp only [Atom.unmasked,Slot.atSite,hv]
   simp_rw [uncut,he]; exact Equiv.sum_comp (Equiv.addRight b) (fun x:Site n=> ∑' i,(p i).unmasked U x)
lemma raw_coast (p:ℕ→Atom G r)(U:Config G n)(s:Signed)(b:Site n): orbitRaw p (pull s b U)=orbitRaw p U:= by
   unfold orbitRaw; simp only [pull_pull,affine, Signed.act_zero,zero_add]; unfold Patch.average
   apply congr_arg (fun x:ℝ=> (Fintype.card Signed:ℝ)⁻¹*x)
   refine Eq.trans (Finset.sum_congr rfl (g:=fun i=> uncut p (pull (s*i) 0 U)) ?_) (Equiv.sum_comp (Equiv.mulLeft s) (fun i:Signed=> uncut p (pull i 0 U)))
   intro i _; let c:=s*i; have h:pull c b U=pull 1 (c⁻¹.act b) (pull c 0 U):= by rw [pull_pull]; simp [affine]
   change uncut p (pull c b U)=_; rw [h, uncut_coast]
def mountain (p:ℕ→Atom G r)(n:Side)(e:ℕ): Pap (wire G n):= X^e* afterX (paste (turnSeries p)) r
lemma uncut_leak {p:ℕ→Atom G r} (h:AtomWall p σ A)(x:Site n)(s:Signed)(U:Config G n)(k:Site n→G.El): orbitRaw p (Lattice.gauge k (pull s x U))=orbitRaw p U:= by
   rw [← raw_coast p U s x];unfold orbitRaw;simp_rw [Work.F05.pull_gauge_zero,Work.F05.uncut_gauge p h.2]
lemma uncut_moans (p:ℕ→Atom G r)(h:AtomWall p σ A)(hs:0<σ)(i:ℕ)(hi:i<r): coeff i (paste (turnSeries p (m:=n)))=0:= by
   have he:= (rays_jet (turns_analytic p hs h.1 (m:=n)) _).1 (turns_low p hs h.1) i hi
   rw [←beam_price,show beam (turnSeries p (m:=n)) i=0 from ?_,map_zero];funext v;rw [beam,Tensor.coeff,he,smul_zero];rfl
lemma uncut_civic (p:ℕ→Atom G r)(h:AtomWall p σ A)(hs:0<σ)(n:Side)(e:ℕ): Civic (mountain p n e):= by
   have H:= turns_analytic p hs h.1 (m:=n); intro s x I inst v w k hv hw hV hW _ _ hz
   let f:Link G n→ℝ:= turnSeries p
   have ht : f ∘ v =ᶠ[𝓝 0] f ∘ w:= hz.mono fun b hb=> by change orbitRaw p _= orbitRaw p _; rw [hb]; exact (uncut_leak h x s _ _).symm
   let a:= mountain p n e; have HZ : X^r*a=X^e*paste f:= by unfold a;rw [mountain,mul_left_comm, after_rope _ _ (uncut_moans p h hs)]
   apply mul_left_cancel₀ (pow_ne_zero r PowerSeries.X_ne_zero); calc
      X^r * roam ℝ (motor v) a = roam ℝ (motor v) (X^r*a):= by rw [map_mul,map_pow,show roam ℝ _ X=X from change_X _]
      _ = roam ℝ (motor w) (X^r*a) := by rw [HZ,map_mul,map_mul,map_pow,map_pow,show roam ℝ (motor v) X=X from change_X _,show roam ℝ _ X=X from change_X _,← paste_steps _ v H.contDiffAt (hV.of_le le_top) hv,← paste_steps _ w H.contDiffAt (hW.of_le le_top) hw,paste_replace ht]
      _ = X^r * roam ℝ (motor w) a := by rw [map_mul,map_pow, show roam ℝ _ X=X from change_X _]
-- Tail data all grades; output consumer uses at fixed e only
structure FloatK (T: Pot G): Prop extends Vivid T where
    fare : ∀ j r,∃ σ C, 0<σ ∧ Bail (fame _) σ (T j r) C
    civic: ∀ n,Civic (stone T n)
structure Fits (T:Pot G)(E:ℕ)(σ C:ℝ):Prop where
    money:0≤C
    pay:∀ e≤E,∀ i,Bail (fame _) σ (T e i) C
variable {T S: Pot G}{η B C:ℝ}
lemma Fits.mono (h: Fits T E σ B)(he:η≤σ)(ht:B≤C): Fits T E η C:= ⟨h.money.trans ht,fun _ h' k=> ((h.pay _ h' k).shrink he).mono ht⟩
lemma Fits.add (h:Fits T E σ A)(e:Fits S E σ B): Fits (T+S) E σ (A+B):= ⟨add_nonneg h.money e.money,fun i h' k=> (h.pay i h' k).add (e.pay i h' k)⟩
lemma Fits.sub (h:Fits T E σ A)(e:Fits S E σ B): Fits (T-S) E σ (A+B):= ⟨add_nonneg h.money e.money,fun i h' k=> (h.pay i h' k).sub (e.pay i h' k)⟩

-- any sequence of matched prices. ε rank bounds match requisition.
variable (p:ℕ→ Atom G (t+1))(u:ℕ)(V:(r:ℕ)→Tile (edgeL G) (r+1))
def snowcap (V:(r:ℕ)→Tile (edgeL G) (r+1))(t u:ℕ):Pot G:= fun e r=> match r with
    | 0 => 0
    | k+1 => if u≤ e ∧ k+u=t+e then V k else 0
variable (hp:t+1 ≤ u+2)(hv:(t+1)%2=u%2)(H:AtomWall p σ A)(hs:0<σ)(ht:∀ r,Matched (V r) (fun n=> turnSeries p (m:=n)))(he:∀ r,Up (V r)) {U K:ℕ→ ℝ}(hz:∀ r,0<U r)(HH:∀ r,Bail (fame _) (U r) (V r) (K r))
include hp hv H hs ht he HH hz
lemma vivid_cap : Vivid (snowcap V t u):= by
   constructor
   · intro e r; cases r
     · apply up_zero
     next r=> unfold snowcap; dsimp only; split; exact he _;exact up_zero _
   · intro e r; cases r
     · apply agate_zero
     next r=> unfold snowcap;dsimp only;split; exact Matched.agate (he _) (HH _) (hz r).le (ht r) (fun _=>turns_analytic p hs H.1); exact agate_zero _
   intro e r a;cases r
   · exact (a rfl).elim
   next r=> unfold snowcap at a; dsimp only at a;split at a <;> first|omega|contradiction
omit hv H hs he HH hz in lemma snow_stamp (n:Side): stone (snowcap V t u) n= mountain p n u:= by
   ext1 e; rw [sow_coeff, mountain, coeff_X_pow_mul']; unfold sow; split
   next he'=>
      rw [Finset.sum_eq_single (t+(e-u)),snowcap,if_pos (by omega)]
      · rw [ht _ n, beam_price, after_one,Nat.succ_add]
      · intro b _ h; rw [snowcap,if_neg (by omega),cum_zero,map_zero]
      · intro hh; exact (hh (Finset.mem_range.mpr (by omega))).elim
   next he'=> apply Finset.sum_eq_zero; intro i _; rw [snowcap,if_neg (by omega),cum_zero,map_zero]
-- unnecessary variables omit
lemma snow_warm : FloatK (snowcap V t u):= { vivid_cap p u V hp hv H hs ht he hz HH with
   fare:= fun j r=> by
       cases r
       · exact ⟨1,0,one_pos,bail_void ..⟩
       next r=> unfold snowcap;dsimp only;split;exact ⟨_,_,hz _,HH _⟩; exact ⟨1,0,one_pos,bail_void ..⟩
   civic:= fun n=> snow_stamp p u V hp ht n ▸ uncut_civic p H hs n u }
end YM.FormalBulk08.Broc
