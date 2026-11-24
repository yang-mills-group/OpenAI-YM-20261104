import YM.WilsonBridge.SumEnd
/-!
# Literal Wilson scalar pinned observables in the θ and momentum alphabets

No ghost exact terms in a `Pin`. It fixes the same Wilson O and translates it on
all periodic volumes including before inversion. `glyph` uses the actual Menu API;
specifying particular realizations with an a priori stencil requires supplying pins
rather than choosing unspecified representatives of germs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBridge
open MS MS.Book MS.Koszul MS.Swirl MS.Puff MS.Cylinder MS.Orbit
open MS.Book.Convolve Program Puff.Mom Puff.Engine Puff.SplitP Puff.Actors Puff.Dynamics Orbit.LogReal Orbit.Cog
open Function Finset
open scoped BigOperators ContDiff Topology
open PeriodicEnd Lattice Full Injections Based Based.Position Plane City Tone Native Native.Chart Native.Wilsonian MS.Fleet FreeBV Near
open Lab Taylor Menus PertExtension Orb
variable {G:Gauge}{n:Side}
local notation "χ"=> Native.Chart.drive n
local notation "V"=> Full.Index G n
local notation "π"=> Position.Parity G n
local notation "ν"=> direction ( G:=G ) ( P:=Site n )
local notation "pu"=> σbranch ( G:=G ) ( n:=n )
local notation "Φu"=> promote (pull (Ux G n))
local notation "Fv"=> promote (pull ( GU G n ))
/-- Pin identifies a literal Wilson representation (may use exactly a regular section,
 not required a.e. outside the saddle for formal comparison). Invariant even before
 quotient. Minimum rank through every side. -/
structure Pin (G:Gauge) where
    power : ℕ
    F : Dot G Cover
    func : (n:Side)→ Wilson.Config G n→ℝ
    fixed (n:Side) : Native.Chart.OpenGauge ( Native.Chart.drive n ) (func n)
    smooth (n:Side) : germ (func n ∘ Native.Chart.nation)
    packed (n:Side) : enters n F= Native.reads (func n ∘ Native.Chart.nation)
    low (n:Side) : From (enters n F) power
-- position translation before restricting to inversion.
def offset (v:Site n)(e:Lattice.Edge (Site n)) : Lattice.Edge (Site n):= (v+e.1,e.2)
def translated (v:Site n) (O:Wilson.Config G n→ℝ)(f:Wilson.Config G n) := O (f ∘ offset v)
private abbrev liquid (v:Site n)(X:Site n):= v+X
private def remaps (v:Site n) : aFull G n→ₗ[ℝ] aFull G n:= LinearMap.pi fun x=> LinearMap.proj (offset v x)
lemma contractO (v:Site n)(O:Wilson.Config G n→ℝ): translated v O ∘ Native.Chart.nation=(O∘ Native.Chart.nation) ∘ remaps v:=rfl
lemma trans_f {O:Wilson.Config G n→ℝ}(h: Native.Chart.OpenGauge χ O)(v:Site n): Native.Chart.OpenGauge χ (translated v O):= by
   intro g A; unfold translated; rw [show Native.Chart.siteGauge χ g A∘offset v=Native.Chart.siteGauge χ (g∘ liquid v) (A∘ offset v) from ?_,h]; funext i; unfold Native.Chart.siteGauge offset Native.Chart.endRail Function.comp liquid; dsimp only; rw [add_assoc]
lemma full_gauge {O:Wilson.Config G n→ℝ}(h: Native.Chart.OpenGauge χ O) : Position.Invariant O:= by
    intro t _ U; rw [ show Lattice.gauge t U= Native.Chart.siteGauge χ (fun x=>(t x)⁻¹) U from funext (fun i=> by rw [Lattice.gauge, Native.Chart.siteGauge, inv_inv ]; rfl), h ]
-- translate Lab.Shift stencil
private lemma dir_shift (v:Site n)(i: V): remaps (G:=G) v (ν (post ( liquid v ) i))=ν i:= by
   rcases i with ⟨⟨⟨_|i,_|_⟩,t⟩,p⟩ <;> first| exact map_zero _ | skip
   funext x; rcases x with ⟨x,j⟩; change priv ((v+p,i),t) (v+x,j)=priv ((p,i),t) (x,j); simp [priv,Pi.single_apply]
private def postEq (v:Site n): Equiv.Perm (Mode (BH G) (Site n)):= Equiv.prodCongr (Equiv.refl _) (Equiv.addLeft v)
lemma enter_shift (q:Cover)(F:Dot G Cover) : Lab.Shift ( wrap n q ) (shown n F)= shown n (Lab.Shift q F):= ( trans_shift F _ ( wrap n ) ).symm
lemma from_shift {q:ℤ}{v:Dot G Cover} (z:Cover)(h:From ( enters n v ) q) : From ( enters n (Lab.Shift z v)) q:= by
    intro l he; change (shown n _).val l=_; rw [ ← enter_shift z ]; let P:= postEq ( G:=G ) (wrap n z); let k:=l.map P.symm
    have hh: k.length=l.length:= List.length_map ..; rw [show l=k.map ⇑P from ?_]; swap; · simp [ k, List.map_map ]; -- inspect
    exact (without (post (liquid (wrap n z))) P.injective (F:=shown n v) k).trans (h k (hh ▸ he)) -- signature/metas
namespace Pin
variable (p: Pin G)
-- explicit anchor. a differentiability after Wrap. This is enough for finite-formal, not analytic remainder
abbrev charged (n:Side)(z:Cover) := translated (wrap n z) (p.func n)
lemma inkP (z:Cover): germ (p.charged n z ∘ Native.Chart.nation):= by
    rw [charged,contractO]; let K:= (remaps (G:=G) (wrap n z)).toContinuousLinearMap; refine ContDiffAt.comp ( f:=K ) (g:= p.func n ∘ Native.Chart.nation) (0:aFull G n) ?_ K.contDiff.contDiffAt; rw [map_zero]; exact p.smooth n
lemma dressed (z:Cover) : enters n (Lab.Shift z p.F)= Native.reads (p.charged n z ∘ Native.Chart.nation):= by
    unfold charged; rw [contractO]; let K:= (remaps (G:=G) (wrap n z)).toContinuousLinearMap
    change ( shown n (Lab.Shift _ _) ).val= ink direction ( (p.func n ∘ Native.Chart.nation) ∘ K ); rw [ink_ctrl_one ν K (p.smooth n), ← enter_shift ]; let T:= postEq ( G:=G ) (wrap n z)
    have ht (f:aFull G n→ℝ)(l:List V) : ink ( K∘ ν ) f (l.map T)= ink ν f l:= by
        induction l generalizing f with| nil=>rfl| cons i l ih=> rw [ List.map_cons, ink, ink, show ( K∘ ν ) ( T i )=ν i from dir_shift _ i, ih ]
    funext l; have hh:l=(l.map T.symm).map T:= by simp
    rw [hh,ht, ← show (shown n p.F).val=ink ν (p.func n ∘ Native.Chart.nation) from p.packed n ]; exact without (post (liquid ( wrap n z ))) _ T.injective ..
-- `ΜΘ` raw based rank, basis pull exactly insertion. no constant subtraction.
lemma p_in (z:Cover) : pull ( Ux G n ) (enters n ( Lab.Shift z p.F ))=Position.insertion ( p.charged n z ):= by
    rw [p.dressed]; unfold Native.reads; rw [pigment (p.inkP z)]; apply congr_arg; funext i; rw [charted]; change _= (p.charged _ _) (array i); rw [array_full]; rfl
lemma initI (z:Cover) : From (Position.insertion ( p.charged n z )) p.power:= by rw [← p.p_in ]; exact pull_from _ (from_shift _ (p.low n))

-- constructor via any actual O realizing the Aura. Only uses its finite formula.
def of_aura {G:Gauge} {F:Dot G Cover}{d:ℕ}(h:Studio.Aura F d) : Pin G:= {
    power:=d
    F:=F
    func n:=( h.pay n ).choose
    fixed n:= ( h.pay n ).choose_spec.1
    smooth n:= ( h.pay n ).choose_spec.2.1
    packed n:= ( h.pay n ).choose_spec.2.2
    low n:= Book.from_pass n h.low }
def glyph {B:Local.Physical.Deck G}(U: LitBook B){d:ℕ}(i:Glyph B d): Pin G:= Pin.of_aura (U.levels i.size i.grade i.2.2)
end Pin
end YM.WilsonBridge
