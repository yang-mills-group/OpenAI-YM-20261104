import YM.MS.Orbit.Sheen
/-!
# Finite Fourier-polynomial projected calculus. The physical reading in the orb uses these kernels.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit
open Set Function Filter Finset Metric MeasureTheory
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City Latch Job Belt Flux Cog Wire Rake Book Convolve
open scoped Topology ContDiff Interval
variable {G:Gauge}{W I E:Type}{n:Side}
namespace LogReal
-- no H.B glow required for definition. labels position shifts supplied independently as raw kernels.
variable {A:Type}[Fintype A]
abbrev Series (A:Type):= ℕ→OM A
abbrev SpecB (A:Type) := ℕ→BL A
abbrev Lines (A:Type):= ℝ→ Grain A
abbrev Mate (A W:Type):= Finset W→ ℕ→ BL A
abbrev Static (K:Lines A)(F:OM A): OM A:= fun t=> frame ( K t ) ( F t )
abbrev TypeTouch (p:Sector A)(P:Lines A)(F H:OM A): OM A:= fun t=> conn p (P t) (F t) (H t)
abbrev Level (p:Sector A)(P:Lines A)(F H:Series A)(n k:ℕ):= pathU (TypeTouch p P) n k F H
abbrev Fill (L: Lines A)(V:BL A)(F H:OM A): Prop:= F 0=V ∧ Status F (Static L F + H)
def Background (p:Sector A)(L:Lines A)(Q:SpecB A)(B: Series A): Prop:= B 0=0 ∧ ∀ n,0<n→ Fill L ( Q n ) ( B n ) (((2:ℂ)⁻¹) • Level p L B B n 1)
abbrev Infos (W A:Type):= Finset W→ Series A
abbrev Present (b:Bool)(G:Gauge)(n:Lattice.Side): Op ( FixedMode G n ) ℂ:= readerV (iota G n) b
def primary (G:Gauge)(n:Side)(b:Bool)(P:ℝ→Latch.Edge G): Lines (FixedMode G n):= fun t=> Paper n b ( P t )
abbrev normal (G:Gauge)(n:Side)(b:Bool):= primary G n b (LaceL G)
-- Clock.Step uniqueness & translation
variable {K:Lines A}{F H D X:OM A}{V: BL A}
lemma expertise (h:Fill K V F X)(he: Fill K V H X): F=H:= by
   let T(P: over Unit A): over Unit A:= fun i=> Static K ( P i ); let e (P:OM A) : over Unit A:= fun _=> P; have hp {P:OM A}(ht:Fill K V P X): Clocked T (fun _=>V) (e P) (e X):= ⟨ fun _=>ht.1,⟨ by obtain ⟨k,hk⟩:=ht.2.life; exact ⟨k,fun _=> hk⟩, fun _=> ht.2.path ⟩ ⟩; apply congr_fun (modal_uniq (U:=T) ?_ (hp h) ( hp he )) (); intro S B k hQ i t w hw; unfold T Static Cog.frame; simp_rw [LinearMap.sum_apply,Finset.sum_apply, LinearMap.smul_apply,Pi.smul_apply,diffPair_apply,at_D,show ∀ x y:A,S i t (x::y::w)=_ from fun x y=> hQ i t (x::y::w) (by simp; omega)]
variable {Q:SpecB A}{B Z:Series A}{p:Sector A}
lemma just (hp: Background p K Q B)(hv:Background p K Q Z): B=Z:= by
   funext n; induction n using Nat.strong_induction_on with| h n he=>
     by_cases hz:n=0; · rw [hz,hp.1,hv.1]
     obtain ht:0<n:= Nat.pos_iff_ne_zero.mpr hz; obtain hc:= hp.2 n ht; rw [show Level p _ B B n 1=Level p K Z Z n 1 from (Finset.sum_congr rfl fun i hi=> by obtain hv:=early _ _ _ hi; rw [he i hv.2, he (n-i) (by omega)]) ] at hc; exact expertise hc ( hv.2 n ht ) -- parser simp
variable [LinearOrder W]
def labels (p:Sector A)(K:Lines A)(X:Infos W A)(S:Finset W)(k:ℕ): OM A:= ∑ s∈ picks S,∑ n∈ antidiagonal k, TypeTouch p K (X s n.1) (X (S\s) n.2)
def CascadeS (p:Sector A)(K:Lines A)(Q:Mate A W)(B:Series A)(X:Infos W A): Prop:= X ∅=0∧∀ s,s.Nonempty→ ∀ n, Fill K ( Q s n ) ( X s n ) ( Level p K B ( X s ) n 0 + labels p K X s n )
lemma sumLabels {B:Series A}{Q:Mate A W}{ X Y: Infos W A}(hx:CascadeS p K Q B X)(hp:CascadeS p K Q B Y): X=Y:= by
   funext s; induction s using Finset.strongInductionOn with | _ s hf=>
     by_cases hv:s.Nonempty; swap; · rw [Finset.not_nonempty_iff_eq_empty.mp hv,hx.1,hp.1]
     funext n; induction n using Nat.strong_induction_on with| h n hM=>
       obtain hu:= hp.2 s hv n; have hz : Level p K B (Y s) n 0+labels p K Y s n= Level p K B ( X s ) n 0 + labels p K X s n:= by
          refine congr_arg₂ (·+·) ( Finset.sum_congr rfl fun i hi=>?_ ) ( Finset.sum_congr rfl fun i hi=> Finset.sum_congr rfl fun j hj=> ?_); · rw [hM i ( early _ _ _ hi|>.2 )]
          exact congr_arg₂ _ ( (congr_fun ( hf i (n_small hi |>.1 )) _).symm ) ((congr_fun ( hf (s\i) ( n_small hi |>.2.2.2 )) _).symm ) -- indent
       exact expertise (hx.2 s hv n) (hz ▸ hu)
end LogReal
end YM.MS.Orbit
