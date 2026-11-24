import YangMills.WilsonProof.NativeSupport.YM.MS.Puff.State
/-!
# Genuine finite mesh Wick calculus
Use Cap data & Linear ext so raw symbols can be very general (not tied to arity enumeration).
Realization with infinite heat endpoint is still purely perturbative fixed mesh.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Swirl
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Orbit Orbit.Cog Orbit.LogReal Book Convolve Puff Puff.Actors
open scoped Topology ContDiff Interval
variable {I E A:Type}{p:Sector A}{F H:BL A}{n j k:ℕ}{h v:ℤ}{L:Grain A}(K:Grain A)
-- symmetry later. don't restrict evaluation (need track separately for derivatives)
def Mini (A:Type): Submodule ℂ (BL A):={
   carrier:={F|∃ q:ℕ, Limit F q}
   zero_mem':= ⟨0,fun _ _=> rfl⟩
   add_mem' := fun h hc=> by obtain ⟨j,h⟩:=h; obtain ⟨k,hv⟩:=hc; exact ⟨ max j k, ( h.up (by omega)).add (hv.up (by omega)) ⟩
   smul_mem':= by intro c F h; obtain ⟨k,h⟩:=h; exact ⟨ k,h.smul c ⟩ }
lemma minH (h:Limit F v): F∈ Mini A:=⟨ v.toNat,h.up (by omega) ⟩
lemma miD (h:F∈ Mini A)(i:A): D i F∈ Mini A:= by obtain ⟨k,h⟩:= h; exact minH (h.tip i)
lemma tower (F: Mini A): ∃ n:ℕ,Limit F.val n:= F.property
lemma miPair (h:F ∈ Mini A)(he:H∈ Mini A): product p F H∈ Mini A:= by obtain ⟨k,h⟩:=h; obtain ⟨l,hv⟩:=he; exact minH ( h.pair hv )
variable [Fintype A]
local notation "Kκ"=> Orbit.Cog.frame K
lemma lapS (h:Symm p F): Symm p ( Kκ F ):= by unfold Cog.frame; simp_rw [ LinearMap.sum_apply, LinearMap.smul_apply ]; exact Symm.sum _ fun i _=> Symm.sum _ fun j _=> ((h.drop i).drop j).smul _
lemma brush (i:A)(hc: Clear p K)(h:Symm p F): D i ( Kκ F ) = Kκ ( D i F ):= by
   unfold Cog.frame; simp_rw [ LinearMap.sum_apply, LinearMap.smul_apply, diffPair_apply, map_sum,map_smul ]; refine Finset.sum_congr rfl fun x _=> Finset.sum_congr rfl fun y _=>?_ ; by_cases hp: K x y=0; simp [hp]; obtain he:= hc _ _ hp; rw [ ( h.drop x ).commute i y,h.commute i x,map_smul, he, ← mul_smul (cross (p y) (p i):ℂ), cross_cross,one_smul ]
lemma fpΩ (F:BL A): frame L F=∑ i,∑ j,L i j • diffPair i j F:= by unfold frame; simp only [ LinearMap.sum_apply,LinearMap.smul_apply ] -- preserve abbreviation
lemma survey (hc: Clear p K)(h:Symm p F): frame L ( Kκ F )=Kκ ( frame L F ):= by rw [fpΩ (L:=L),fpΩ (L:=L)]; simp_rw [map_sum,map_smul]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> ?_; rw [diffPair_apply,diffPair_apply, brush K i hc h, brush K j hc (h.drop i) ]
lemma rebate (hF: Limit F h): Limit (Kκ F) (h-2):= by
    unfold Orbit.Cog.frame; simp_rw [ LinearMap.sum_apply,LinearMap.smul_apply ]; rw [ show h-2=h-1-1 from (by omega) ]; exact Limit.sum _ fun i _=>Limit.sum _ fun j _=> ( (hF.tip i).tip j ).smul _
-- convention.K pair.Data
abbrev tep (n:ℕ): Op A ℂ:= (Actors.phase n) • Kκ ^ n
lemma rise : tep K 0=1:= by simp [tep,Actors.phase]
lemma teen : ( tep K (n+1) ) F= ((n+1:ℂ)⁻¹) • Kκ ( tep K n F ):= by unfold tep; simp_rw [ LinearMap.smul_apply,map_smul,Dynamics.phase',mul_smul,pow_succ',Module.End.mul_apply ] -- cast
lemma te2 (hF:Symm p F): Symm p ( tep K n F ):= by induction n with| zero=> rw [rise]; exact hF| succ n ih=> rw [teen]; exact Symm.smul _ (lapS K ih)
lemma té_D (hc: Clear p K)(hF:Symm p F)(i:A): D i (tep K n F)= tep K n ( D i F ):= by induction n with| zero=> rw [rise]; rfl| succ n ih=>rw [teen,teen,map_smul,brush K i hc (te2 K hF), ih]
lemma te2H (hF:Limit F h): Limit (tep K n F) (h-2*n):= by induction n with| zero=> rw [rise]; simpa using hF | succ n ih=> rw [teen,show h-2*((n+1:ℕ):ℤ)=h-2*n-2 from (by omega) ]; exact Limit.smul _ ( rebate K ih )
lemma te2oh (hF: Limit F n)(h:j*2>n): tep K j F=0:= funext fun l=> te2H K hF l (by omega)
-- Need operator H not used at n if equal `j=n+1`.
def effect (K:Grain A)(n:ℕ): Op A ℂ := ∑ i∈Finset.range ( n+1 ), tep K i
lemma ahead (hF:Limit F n)(hc:n≤j): effect K n F= effect K j F:= by
   rw [effect, LinearMap.sum_apply,effect,LinearMap.sum_apply]; apply Finset.sum_subset; exact Finset.range_mono (by omega); intro i hi hv; exact te2oh K hF (by simp at hv hi; omega)
def most (f: Mini A): ℕ:= ( tower f ).choose
omit [Fintype A] in
lemma c_most (f: Mini A): Limit f.val (most f):= ( tower f ).choose_spec
lemma atŴ (f: Mini A) (hF:Limit f.val n): effect K ( most f ) f.val= effect K n f.val:= by rw [ahead K hF ( show n ≤ max n (most f) from le_max_left .. ), ahead K (c_most f) (show most f≤ _ from le_max_right n (most f))]
def rightMini (K:Grain A): Linear ( Mini A ) (BL A):={
   toFun f:= effect K (most f) f.val
   map_add' := fun f g=> by
       let n:=max (most f) (most g); have hf : Limit f.val n := (c_most f).up (by exact_mod_cast le_max_left ..); have hg: Limit g.val n:= (c_most g).up (by exact_mod_cast le_max_right ..); rw [atŴ K (f+g) (show Limit ( f+g ).val n from hf.add hg),atŴ K f hf, atŴ K g hg, Submodule.coe_add,map_add ]
   map_smul':= fun c f=> by rw [atŴ K (c • f) (show Limit ( c • f ).val (most f) from Limit.smul c (c_most f)), Submodule.coe_smul,map_smul]; rfl }
def Shot (K:Grain A): Op A ℂ:= (rightMini K).comp (Mini A).subtype.leftInverse
lemma shot_turned {V: Mini A}: Shot K V.val = effect K (most V) V.val:= congr_arg (rightMini K) (LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr (Mini A).subtype_injective) V)
lemma dawn (hV: Limit F n): Shot K F= effect K n F:= Eq.trans (shot_turned K ( V:=⟨ F,minH hV ⟩ )) (atŴ K _ hV)
-- scalar channel
abbrev View (K:Grain A): Linear ( BL A ) ℂ:= (LinearMap.proj (R:=ℂ) (i:=[])).comp ( Shot K )
lemma bornView {F: Mini A}: View K F.val = effect K (most F) F.val []:= congr_fun ( shot_turned K ) []
omit [Fintype A] in
lemma coinN (z:ℂ): Limit (coin z (A:=A)) (0:ℕ):= fun l h=> by cases l with | nil=> simp at h| cons a l=> rfl
lemma minView (z:ℂ): View K (coin z)=z:= by change Shot K _ []=_; rw [ dawn K (coinN z) ]; simp [ effect,rise, coin ]
end YM.MS.Swirl
