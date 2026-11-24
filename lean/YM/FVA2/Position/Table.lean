import YM.FVA2.Position.Browse
import YM.MS.Garment.Quanta
import YM.MS.Mach.Land
import YM.MS.Theater.DataK

set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Position.OpenAxis
open Function Set Filter Finset MeasureTheory
open MS MS.Plane MS.Koszul MS.Motif MS.Arts MS.Garment MS.Halo MS.Mach
open MS.Landau MS.Book MS.Color MS.Lifting MS.Native
open Analysis Tensor Maxwell Labels MS.Theater
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace Classical
variable {J:Type} {G:Gauge} {m n h:ℕ} {x:E4} {z:ℂ} {a b c:Axis}
lemma total {f:J→Mield G m}(s:Finset J)(h:∀ i∈s,Apple (f i)): Apple (∑ i∈ s,f i) := by
    intro ξ i; simp_rw [ Finset.sum_apply, map_sum ]; rw [Finset.sum_congr rfl (fun j hj =>h j hj ξ i), Finset.sum_comm]; simp only [Finset.smul_sum]
lemma growsG (k:ℕ)(x:E4): Apple (graft (m:=m) (G:=G) z a b x k):= by induction k with| zero=> exact Apple.spicy (chair m a) (chair m b)| succ k ih=> rw [graft]; exact total _ (fun j _=> (Apple.heat _ ih).smul ( ( x j:ℝ ):ℂ ) ) -- Apple.spicy args ?
lemma palette : Apple (Ray G m n z a x):= ( total _ (fun j _=> (growsG n x).smul ( (x j:ℝ ):ℂ ) ) ).smul (↑((slotDen n)⁻¹):ℂ)
local notation "Z"=> asC G h
local notation "L"=> Ramp G h
local notation "Λ"=> Taylor.paint
lemma coats (ξ:G.El)(i:G.ColorIndex): (Prong a x i).comp (Λ ξ)=∑ j:G.ColorIndex,(weight ξ j i) • Prong a x j (h:=h):= by
    apply LinearMap.ext; intro X; change (G.adjoint ξ (X.value a x)) i=_; rw [MS.Native.Paint.acts_all]; rw [LinearMap.sum_apply]; rfl
lemma paintC (ξ:G.El)(X:Coord G h): repeatC ξ (L (Z X) z m)= L (Z ( X.comp (Λ ξ))) z m:= by
   have he:X∈ Submodule.span ℝ (Samples G h):= by rw [many]; exact Submodule.mem_top
   refine Submodule.span_induction (p:=fun X _=> repeatC ξ (L (Z X) z m)= L (Z ( X.comp (Λ ξ))) z m) ?_ ?_ ?_ ?_ he
   · rintro _ ⟨a,x,c,rfl⟩; rw [ramp_Jrad,palette ξ c,coats]; simp_rw [map_sum,map_smul,Finset.sum_apply]; refine Finset.sum_congr rfl (fun j _=>?_); rw [show weight ξ j c • Z (Prong a x j)= wc ξ j c • Z (Prong a x j) from rfl, map_smul, Pi.smul_apply,Pi.smul_apply,ramp_Jrad]
   · change (repeatC ξ _)= L (Z ( (0:Coord G h).comp (Λ ξ))) _ _; simp
   · intro f g h hx ht hm; simp only [map_add,LinearMap.add_comp,Pi.add_apply,ht,hm]
   intro c v H hv; rw [map_smul, LinearMap.smul_comp,map_smul Z]; simp_rw [show ∀ x:Witness G h, L ( c • x)=(c:ℂ) • L x from fun _=>map_smul L (c:ℂ) _,Pi.smul_apply,map_smul,hv]
lemma pigment (f:Pol G)(ξ:G.El): repeatC ξ (seed G f z m)= seed G (changed (fun _=> Λ ξ) f) z m:= by
   induction f using MvPolynomial.induction_on with
   | C a=> rw [changed,MvPolynomial.aeval_C,MvPolynomial.algebraMap_eq, sightC,Mach.Safe.cpig]
   | add f g h k=> simp only [map_add,Pi.add_apply,h,k]
   | mul_X f i ih=> rw [map_mul (changed (fun _=> Λ ξ)),seed_p,seed_p,show repeatC ξ (bite m G _ _)=_ from glob_prod (n:=m) ξ _ _,ih, seed_x, show changed (fun _=> _) (MvPolynomial.X i)=_ from Theater.moved_v (fun _=> Λ ξ) i, Vtheta, sampleC,paintC]; rfl
lemma pigment_i (f: Pol G)(he:f∈ Labels.invariantSpace G):∀ ξ:G.El, repeatC ξ (seed G f z m)=seed G f z m:= by
    intro ξ; rw [pigment,show changed (fun _=> Λ ξ) f=f from Labels.eval_ext _ _ (fun A=> by rw [eval_changed]; exact he A ξ )]
private def Mean (G:Gauge): Seed G→ₗ[ℝ] Seed G where
   toFun f z n:= Color.mean ( f z n )
   map_add' x y:= funext fun z=> funext fun n=>map_add _ (x z n) (y z n)
   map_smul' c x:= funext fun z=> funext fun n=>map_smul _ (c:ℂ) (x z n)
lemma wing_mean (f:Fin n→Plaq)(σ:Grid G n): Mean G (Pole.wing n f σ)=Pole.saint n f σ:= by
    ext z m w; change (∫ k, repeatC k ( Pole.wing n f σ z m ) w ∂G.probHaar)=_; simp_rw [ Pole.radiant,Finset.sum_apply,Pi.smul_apply ];
    simp_rw [show ∀ (i:Grid G n) (k:G.El)(z:ℂ), (( Lifting.ink k i σ :ℝ):ℂ ) • z=( Lifting.ink k i σ ) • z from fun _ _ _=> rfl]; rw [integral_finsetSum _ (fun i _=> (Lifting.massInk i σ).smul_const _)]; simp_rw [integral_smul_const]; rfl
lemma joins (x:Film0 G h n) : seed G x.val ∈ Gallery G n h:= by
    obtain ⟨ht,he,hx⟩:= (Theater.cinema _).mp x.property; rw [show seed G x.val= Mean G (seed G x.val) from funext fun _=> funext fun _=> Eq.symm (Color.mean_identity ( pigment_i _ he )) ]; suffices H:Course G n h≤ Submodule.comap (Mean G) ( Gallery G n h ) from H (chooses _ ht hx); refine Submodule.span_le.mpr ?_; rintro _ ⟨l,σ,rfl,rfl⟩; rw [SetLike.mem_coe,Submodule.mem_comap,wing_mean]; exact Submodule.subset_span (Set.mem_setOf.mpr ⟨l,σ,rfl,rfl⟩)
open MS.Menus MS.Land MS.Theater MS.Local.Physical -- Physical.Deck
open MS.Motif.Literal -- verify namespace
private lemma presentQ (p:Film0 G h n) : Present (seed G p.val):= can_p _ (chooses p.val (cinema _|>.mp p.property|>.1) (cinema _|>.mp p.property|>.2.2))
lemma ticket_eq (A B:Box (Mob G))(h:∀ z:ℂ,value _ z A=value _ z B): A=B:= by
    apply sub_eq_zero.mp; let X:= A-B; have he z :value (Mob G) z X=0:= by unfold X; rw [map_sub,h,sub_self]
    ext i m w; exact valuedZ X ( Wave.slice w ) (fun z=> by rw [he,map_zero]) i
def invoice (G:Gauge) (h n:ℕ): Film0 G h n→ₗ[ℝ] Box ( Mob G ) where
    toFun x:= ( presentQ x ).choose
    map_add' x y:= ticket_eq _ _ (fun z=>by rw [map_add]; exact Eq.trans (congr_fun (presentQ _).choose_spec z) (by simp_rw [Submodule.coe_add,map_add,Pi.add_apply]; congr 1; exacts [(congr_fun (presentQ x).choose_spec z).symm,(congr_fun (presentQ y).choose_spec z).symm])) -- simp tuple hack
    map_smul' c x:= ticket_eq _ _ (fun z=> by rw [Mach.lng]; exact Eq.trans (congr_fun (presentQ _).choose_spec z) (by rw [ Submodule.coe_smul, show seed G ( c • x.val) = c • seed G x.val from map_smul ((seed G).restrictScalars ℝ) c x.val, show value _ z _=_ from congr_fun (presentQ x).choose_spec z ]; rfl ))
lemma priceR (x:Film0 G h n): value _ z (invoice G h n x)=seed G x.val z:= congr_fun (presentQ x).choose_spec z
lemma invoiceC (x:Film0 G h n): Ele h n ( Theater.orbit G x.val ) (invoice G h n x):= by
    refine ⟨ by simp_rw [priceR]; exact joins x ,?_⟩; exact congr_fun (( low_row (invoice G h n x) ).symm.trans (priceR (z:=0) x)) 0 |>.trans (stake _)
def Plot (V:Deck G): Booked V where
    optics _ i:= invoice _ _ _ ( Theater.Resume V _ _ ( Module.finBasis ℝ _ i.2 ))
    law d i:= by change Ele d i.1.val ( V.raw d i.1.val i.2 ) _; rw [ ← Theater.lamp_here V i.2 ]; exact invoiceC ( Theater.Resume V d i.1.val ( Module.finBasis ℝ _ i.2 ) ) -- dep equality proof
end YM.FVA2.Position.OpenAxis
