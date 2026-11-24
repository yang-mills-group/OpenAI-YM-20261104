import YM.MS.Menus.Tape
import YM.MS.Menus.Mark
import YM.MS.Menus.Quantify
import YM.FVA2.Full.Glyph
/-! FVA_2 addition: `FullBook` with W-type shifts.
Module Tape. Relevant proofs extended from `LitBook` in
YM.MS.Menus.Tape
YM.MS.Menus.Mark
YM.MS.Menus.Quantify.
Main stencils/rank/affordability modified in `YM.FVA2.Full.Glyph`.
Names with `F` suffix are generally for the adjusted versions.
No changes to `PhysicalSum`, BV prescription or `MS_Data`. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Menus
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Momentum Orient Draft Sew Native.Chart Tone Tone.Frame
open Color Lifting Local Local.Physical Submodule Logarithm High Ghost
open Book Convolve Program Flux Native.Wilsonian Native.Studio Paint
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{B: Deck G} (V : FullBook B)(p:Team) {d:ℕ}
variable (A:Acts B d)
def rentF (x:ℝ) (i:ℕ): Dot G Cover:= ∑ g:Glyph B d, ∑ d∈antidiagonal i, oil A g d.1 x • Glyph.preambleF V p g x d.2
def scoreF (x:ℝ): T (Dot G Cover):= rentF V p A x + motto p A x
lemma markSenseF (x:ℝ) : scoreF V p A x= rentF V p A x+ steadyE (Spectrum G) (style G p x) (prim A x):= rfl
lemma steadyF (k:ℕ) (P:Acts B d) (H:∀ i, i≤ k→ A i=P i) (x:ℝ): scoreF V p A x k=scoreF V p P x k := by
    simp_rw [scoreF,Pi.add_apply,sky,rentF, H k k.le_refl]
    apply congr_arg₂ (·+·)
    · apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j hj; unfold oil; rw [H j.1 (by obtain h:=mem_antidiagonal.mp hj; omega)]
    congr 1; apply Finset.sum_congr rfl; intro j hj; rw [H j.2 (by obtain h:=mem_antidiagonal.mp hj; omega)]
lemma posesF (x:ℝ)(i:ℕ): Tuned (rentF V p A x i) 0:= Tune.sum _ fun g _=> Tune.sum _ fun j _=> (Glyph.pre_cF V p g x j.2).cash _ (show star (oil A g j.1 x)=_ from by simp [oil])
lemma appearsF (x:ℝ)(i:ℕ): Colorless (rentF V p A x i):= Colorless.csum _ fun g _=> Colorless.csum _ fun j _=> (Glyph.pre_litF V p g x j.2).smul _
lemma rentReadyF (i:ℕ): Ready (fun x=> rentF V p A x i):= value_sum _ (fun j _=> value_sum _ (fun k _=> pc_ready (c:=oil A j k.1) ⟨_,Ready.got _,rfl⟩ (Glyph.pre_readyF V p j k.2)))
lemma rentLimitF (x:ℝ)(i:ℕ): Limit (rentF V p A x i).val (i+d):= by unfold rentF; simp_rw [sum_stack]; exact Limit.sum _ (fun g _=> Limit.sum _ (fun k hk=> ((Glyph.pre_costF V p g x k.2).smul _).up (by obtain he:= Finset.mem_antidiagonal.mp hk; have hv:= Glyph.memory g; omega)))
lemma rangeF (x:ℝ)(i:ℕ): Limit (scoreF V p A x i).val (i+d+fringe A i):= Limit.add ((rentLimitF V p A x i).up (by omega)) ((stuff p A x i).up (by omega))
lemma decorF : Circle G (scoreF V p A) false 0 where
    stance0 _ _ h:= False.elim (Bool.noConfusion h)
    actual i x:= (posesF V p A x i).add (pretty p A x i)
    settled i x:=(appearsF V p A x i).add (colorRoot p A x i)
    tag i:= (rentReadyF V p A i).add (flows p A i)
    room i:=⟨i+d+fringe A i,fun x=>by exact_mod_cast (rangeF V p A x i)⟩
end YM.MS.Menus
end
set_option autoImplicit false
noncomputable section
namespace YM.MS.Menus
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Momentum Orient Draft Sew Native.Chart Tone Tone.Frame
open Color Lifting Local Local.Physical Submodule Logarithm High Ghost
open Book Convolve Program Flux Native.Wilsonian Native.Studio Paint
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{B: Deck G}(V : FullBook B)(p:Team) {d n:ℕ} (x:ℝ)
section close
variable (A:Acts B d)(H:G.Simple)
include H
lemma rentedF : Weightless (Spectrum G) (style G p x) (rentF V p A x):= by
    let P:=Spectrum G; let T:Glyph B d→ T (Dot G Cover):= fun i=> Glyph.preambleF V p i x;
    let U (ζ:Glyph B d)(n:ℕ) := oil A ζ n x; let X := style G p x; let D:=actB (Spectrum G)+ pairW (Spectrum G).touch X; let J:= pairW (LinearMap.lsmul ℂ (Dot G Cover));
    have he c f: actB P (J c f)=J c (actB P f):= by funext n; unfold actB J; simp only [paired,promised, LinearMap.lsmul_apply,map_sum,map_smul]
    have hd (i:Glyph B d): D (J (U i) (T i)) =0:= by rw [show D (J (U i) (T i))=J (U i) (D (T i)) from ?_,show D (T i)=0 from Glyph.pre_freeF V p i x H,map_zero]; unfold D; simp only [LinearMap.add_apply, olio, J,map_add]; rw [show actB (Spectrum G) _ =_ from he (U i) (T i)]
    change D _=0; rw [show rentF V p A x=∑ g:Glyph B d,J (U g) (T g) from funext fun n=> by unfold rentF; simp only [Finset.sum_apply]; rfl,map_sum]; simp_rw [hd,Finset.sum_const_zero]
lemma lawF : Weightless (Spectrum G) (style G p x) (scoreF V p A x):= by
    let Q := actB (Spectrum G)+ blocks (Spectrum G) (style G p x); change Q (rentF V p A x+motto p A x)=0
    have hh : Q (motto p A x)=0 := steady_squares (style G p x) _ (main_law G p x H) (fun i=> ((core_circle G p).actual i x).symm) (fun i=> Tune.parity ((core_circle G p).actual i x) ghostParity) (fun i=> ((A i).proof.actual x).symm)
    rw [map_add,hh,show Q (rentF V p A x)=0 from rentedF V p x A H,zero_add]
end close
def lightingF (Q: Price B d) (x:ℝ): Dot G Cover:= ∑ c:Glyph B d, (↑((Q c).eval x):ℂ) • Glyph.preambleF V p c x 0
variable (A:Acts B d)(Q:Price B d)(X:Power G)
lemma repairF : scoreF V p A x n-scoreF V p (patch A Q X n) x n= lightingF V p Q x + advance (X.input x):= by
   let S:= patch A Q X n; have hc : (A n).proof.input x-(S n).proof.input x = X.input x:= by simp [S,patch,Power.sub]
   have hs (i:Glyph B d) : ∑ j∈antidiagonal n,(oil A i j.1 x - oil S i j.1 x) • Glyph.preambleF V p i x j.2= (↑((Q i).eval x):ℂ) • Glyph.preambleF V p i x 0:= by
        rw [Finset.sum_eq_single (n,0)]; simp [oil,S,patch]
        · intro j hj hne; by_cases h : j.1=n; · obtain ht:=mem_antidiagonal.mp hj; exact (hne (Prod.ext h (by dsimp; omega))).elim
          simp_rw [oil, show S j.1= A j.1 from patch_bef A Q X h,sub_self,zero_smul]
        simp
   rw [scoreF,scoreF,Pi.add_apply,Pi.add_apply, add_sub_add_comm,lightingF]; congr 1
   · unfold rentF; simp_rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro c _; rw [← hs c]; exact Finset.sum_congr rfl (fun k _=> (sub_smul (oil A c k.1 x) (oil S c k.1 x) (Glyph.preambleF V p c x k.2)).symm)
   rw [sky, sky, add_sub_add_comm, ← map_sub,hc,advance]; congr 1
   rw [← Finset.sum_sub_distrib, Finset.sum_eq_single (0,n)]; dsimp only; rw [← map_sub,hc, style,whoZero];
   · intro j hj hne; obtain h :=mem_antidiagonal.mp hj; have h' : j.2≠n:= fun g=> hne (Prod.ext (by dsimp; omega) g); rw [patch_bef _ _ _ h', sub_self]
   simp
end YM.MS.Menus
end
set_option autoImplicit false
noncomputable section
namespace YM.MS.Menus
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Momentum Orient Draft Sew Native.Chart Tone Tone.Frame
open Color Lifting Local Local.Physical Submodule Logarithm High Ghost Detect
open Book Convolve Program Flux Native.Wilsonian Native.Studio Paint
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{B: Deck G}(V : FullBook B)(p:Team) {d n r:ℕ}{v:ℤ}
namespace Glyph
variable {P S:ℝ→ Law G} {Q:Price B d}
lemma hitsF (h: Homes Q v r)(x:ℝ) : Limit (lightingF V p Q x).val r ∧ Fits (lightingF V p Q x) (valAt Q x) r v false:= by
    refine ⟨?_,Fits.sum _ (fun i _=>?_)⟩; swap
    · by_cases he: Q i=0; · simp only [he,Polynomial.eval_zero,Complex.ofReal_zero]; rw [zero_smul,zero_smul]; exact Fits.zero _
      rw [← h.size i he, ← h.grade i he]; exact (Glyph.pre_floorF V p i x).smul _
    unfold lightingF; rw [sum_stack]; refine Limit.sum _ fun c _=>?_ ; by_cases he: Q c=0; rw [he,Polynomial.eval_zero,Complex.ofReal_zero,zero_smul]; exact fun _ _=> rfl; rw [← h.grade c he]; exact Limit.smul _ ((by simpa using pre_costF V p c x 0) : Limit (preambleF V p c x 0).val c.grade)
end Glyph
structure CapacityF (A C:Acts B d)(n r:ℕ)(v:ℤ) (H:ℝ→ Law G): Prop where
    past (i:ℕ): i<n→ A i=C i
    size (x:ℝ): Limit ((scoreF V p A x n)-(scoreF V p C x n)).val r
    jet (x:ℝ): Fits ((scoreF V p A x n)-(scoreF V p C x n)) (H x) r v false

lemma room_hereF (A:Acts B d) {P H:ℝ→ Law G}(h:0≤v)(ht:v≤d)(hp:Ready P)(hq:Ready H) (hc : ∀ i,P i∈B.carries v r)(hd:∀ i,H i∈ Lease G (v-1) r (-1)): ∃ (Q:Price B d) (X:Power G), Glyph.Homes Q v r ∧ X.allowance=r ∧ CapacityF V p A (patch A Q X n) n r v (fun i=> P i+natQ (H i)):= by
    obtain ⟨Q,hQ,hF⟩:= Glyph.offered h ht hc hp; obtain ⟨X,hx,hX⟩:= pens hq hd; have he (x:ℝ): Limit (advance (X.input x)).val r∧ Fits (advance (X.input x)) (natQ (H x)) r v false:= estimateL x (hx ▸ X.ranks x) (hX x)
    refine ⟨Q,X,hQ,hx,⟨fun i h=> (patch_bef A Q X h.ne).symm, fun x=>?_, fun x=>?_⟩⟩ <;> rw [repairF]; exact (Glyph.hitsF V p hQ x).1.add (he x).1; rw [← hF x]; exact (Glyph.hitsF V p hQ x).2.add (he x).2
end YM.MS.Menus
end
