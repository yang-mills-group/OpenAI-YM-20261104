import YM.FVA2.Removal.Accounts
/-!
 # Two-cutoff estimates before imposing a relation between period and spacing

 Theorem `tabulate`. An alternative closing to the one with the $P$ vs $a$ link
 condition already at the outset (see `Register/Pressroom`: `end_to_continuum` also closes in that argument).
 Same physical inputs as used in our comparison. We can even
 impose the estimate using the weakest possible filter on adequately shaped
 trials, e.g. `all_requests`. See also `YM.MS.Tide.assembly` and `CCP` for
 the underlying two-application-of-Fleet method. Pay **source undo** only by
 the volume part! Does not require establishing the bound by integrating a
 single-source-generator interpolation in the quotient. See `Arrival/Net`.

 The period allowance here uses lattice-scale units on length.
 For `T:LPT trial` here use `T.side` (true half), `$θ=log(1/a)$` as usual,
 fixed log reference `μ`, any growth of side. Eventual estimates. To
 expand the estimates in **explicit** two-rate form in physical period use
 `Vol.hard` & `Total.hard` (in Rates). -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Removal
open Function Set Filter Finset Metric MeasureTheory Real
open MS MS.High MS.Koszul MS.Plane MS.Landau MS.Tone Lattice MS.Land MS.Tide MS.Latch MS.Heat MS.Book MS.Book.Convolve Program
open Native Wilsonian MS.Wind MS.Rake MS.Rake.Geo MS.Vista MS.Vane MS.City MS.Orbit Cog MS.Orbit.LogReal
open Puff Engine SplitP Actors Dynamics Puff.Mom MS.Echo
open MS.Fleet MS.Swirl MS.Swirl.Near MS.Menus MS.SpaceOut MS.Dial
open PeakT (ordZ)
open Arrival
open scoped Topology ContDiff Interval
variable {I W:Type}[LinearOrder W] {G:Gauge}{a:I→Cover}{F: MS.Fleet.Terrify W I}{μ:ℝ}{l:Filter I}
variable {K: Land.Booked (Press.portDeck G)}(S: MS_Data G K)(Y:XSpace.Initialize G)(T: Trial I W)
variable (A:Land.Prescription (Press.portDeck G))(u : W→Label (Press.portDeck G))
local notation "p"=> A.team
local notation "φ"=> Press.wickInput Y
local notation "Yr"=> ApplyMF φ A.team A u
local notation "Ur"=> ApplyMF φ ( Stripped A.team ) A u
local notation "Xr"=> PortEntryF φ A ∘ u
local notation "L"=> T.side -- notice unused implicit
local notation "η"=> T.profile.η
local notation "P"=> T.profile
local notation "κ"=> T.head
local notation "co"=> T.off
local notation "H"=> (loose T.profile μ)
local notation "Κ"=> Press.portDeck G
local notation "Ψ"=> goalsK T.off T.profile.η Yr
local notation "Q"=> goalsK T.off T.profile.η (PortEntryF φ A ∘ u)
local notation "h"=> Label.h ∘ u
local notation "Σ_"=> (outside L)
/-- Same Trial of actual placements (including all geometric conditions)
 but drop all requirements on growth of side. -/
structure Fit (T:Trial I W)(μ:ℝ):Prop where
 total: Profile T.profile T.off
 reality i:T.profile.η i=μ-T.profile.θ i
 knit: Mesh T.profile ( Fleet.info T.off )
 clear: Clearance T.side T.head
 wind: Vista.width T.side T.head
omit [LinearOrder W] in
lemma Use_ok (Ux: Dial.Uses T l μ): Fit T μ:= ⟨Ux.total,Ux.reality,Ux.knit,Ux.clear,Ux.wind⟩
/-- Connect source-adjusted and physical columns in one volume-cost pass.
`f` is the connected array for the physical moments (`contact` reconstructs
these moments using the XSpace-side ones), `z` for the comparison using
auxiliary terms for the mark matching. `native` states which kernels are priced.
`fabric`: `X,U` are the cover and orbit families associated to `f`,
`D,E` cover and orbit for `z`. Use the two `Images` there to extract also
the kernel estimates (see also `Certified` for how to do that from `TaylorOKF`).
`B` is on the continuum. In particular `toZ X = toZ D` in the indicated
eventual sense -- we used the simpler source identity on the **cover**, and pay the
source-undo on the **orbit** side by the `Vol` term. Use `Vol.hard` and
`Total.hard` to unpack the `reaches` bounds. -/
structure MenuCost (μ:ℝ)(l:Filter I)(f z: MS.Fleet.Terrify W I) : Prop where
 native (i:I) (x:Finset W):
   PhysicalSum G p (η i) (dimT L i) true x
       (fun w=>co w i) ( κ i ) Ur ( bury i x f ) ∧
   Endμ ( Master G (dimT L i) true ) σbranch
       ( NRG p (η i) ( dimT L i ) G true )
       ( Font σbranch ( ΓM co L i η κ Xr ) x ) ( bury i x z )
 contact (i:I)(x:Finset W):
   bury i x f=Top.value Y u A ( κ i ) (fun w=>co w i) ( dimT L i ) ( η i ) x
 empty:f ∅=0∧ z ∅=0
 fabric: ∃ X U D E B:Rake.Dance G I W,
   SpaceOut.Images G (loose T.profile μ) L η κ Ψ p true X U ∧
   SpaceOut.Images G (loose T.profile μ) L η κ Q p true D E ∧
   CCOrb G η p κ L Ψ true f ∧
   CCOrb G η p κ L Q true z ∧
   (SpaceOut.Folio X (loose T.profile μ) L ∧
    SpaceOut.Folio U (loose T.profile μ) L ∧
    SpaceOut.Folio D (loose T.profile μ) L ∧
    SpaceOut.Folio E (loose T.profile μ) L ) ∧
   DOrd K (frameF I μ) S u (lifted P co) B ∧
   (∀ s:Finset W, s.Nonempty → ∀ n,
     MS.Vane.Verdict (frameF I μ) ( Vane.charge h s ) 0 ( B s n ) ∧
     f s n = toZ U s n ∧ z s n = toZ E s n ∧
     cash_out (loose T.profile μ) L (f s n-toZ X s n) ∧
     cash_out (loose T.profile μ) L (z s n-toZ D s n)) ∧
   (∀ k s, toZ X s k=ᶠ[l]toZ D s k ∧
     PeakT.twin l P mildG (MS.Tide.fare h P (toZ D) s k) (toZ B s k) )
 reaches (s: Finset W) n:
   Tight l P L (MS.Tide.fare h P f s n) (fun i=> book S u μ ( testP T i ) s n ) ∧
   Tight l P L (MS.Tide.fare h P (ordZ f) s n) (fun i=> tour S u μ ( testP T i ) s n) ∧
   Vol l P L (MS.Tide.fare h P f s n-MS.Tide.fare h P z s n)
variable (u0:Fit T μ)(hu:Tendsto T.profile.θ l atTop) (hs:TaylorOKF S (Press.wickInput Y) A) (hg:G.Simple)
set_option quotPrecheck false
include u0 hu hs hg
/-- Uniform (`∀ᶠ i in l`): log spacing eventually large, no side growth condition
required here. Two-term estimate, with the smaller (volume) cost for the source-dependent
undo comparison. See `u0` (`Fit`) for the full geometric assumptions including profile,
separation of placements on the cover and clearance. -/
theorem tabulate : ∃ f z, MenuCost S Y T A u μ l f z:= by -- include h
 obtain hv : WidthW H η co := extent u0.total u0.reality; obtain ⟨hK,hX,hK0,hmenu⟩:= billMenusF u ( «φ»:=φ ) ( A:=A ) hg; have hX0: SpaceOut.FlowSet H Ψ:= moneyM co hv fun i=>⟨ false,0,hK.badge i ⟩; have hXt: SpaceOut.FlowSet H Q:=moneyM co hv (fun i=> ⟨ false,0,hX.badge i ⟩)
 obtain ⟨U,X,f,hI,Fc,hf,h0,hUX,hXU,hpay⟩:= imageBank («P»:=κ) hs.bulk hX0 hv.proper true u0.clear u0.wind
 obtain ⟨E,D,z,hZ,Xc,hz,he,hDQ,hEQ,hpr⟩:= imageBank («P»:=κ) hs.bulk hXt hv.proper true u0.clear u0.wind
 -- exact canonical vs f; tuned physical vs transformed on cover
 have hU(i:I)(s:Finset W): PhysicalSum G p (η i) (dimT L i) true s (fun w=>co w i) ( κ i ) Ur ( bury i s f ):= κglyph co i hK.badge hf (fun _=>billRentF ..) hK0
 let a(i:I)(s:Finset W)(n:ℕ):= toZ D s n i; let w i s n:= toZ X s n i; have HS(k:ℕ)(s:Finset W) : toZ X s k=ᶠ[l]toZ D s k := Filter.EventuallyEq.symm ( Tide.peaks (l:=l) (X:=a) (Y:=w) ( marked W ) Toy ( pointed _ (zeroZ Xc.1)) (fun i=> fun s _ n _=> Submodule.mem_top) ( pointed _ (zeroZ Fc.1)) (fun i s _ n _=>Submodule.mem_top) (fun s n=> MS.Echo.quote (payTune co u0.knit hu) hX hK hs.bulk hg hmenu Xc Fc n s) s k )
 -- on the *same* cover D use the true cover-to-Ms estimate.Then restore dimension powers.
 obtain ⟨U',B,hU',hB,hX'⟩:= CoversF φ S A u P hg u0.knit hs
 have hUe : U'=voyage co D:= Rake.perfect hU' ( BoardingF co (seedW_okF co) Xc (Fleet.fee Xc hXt ) )
 obtain ⟨U'',B',hU'',hB',hX''⟩:= CoversF φ S A u ( frameF I μ ) hg ( posed co u0.knit ) hs
 -- h together
 have ht:= clockShape P (lifted P co) u u0.reality hB' (by rw [←re_n]; exact hB) (fun s hs n=> hX'' s hs n |>.2.1.1 ) -- ann
 have hm(s:Finset W)(n:ℕ): PeakT.twin l P mildG ( MS.Tide.fare h P ( toZ D ) s n ) (toZ B' s n):= by
     by_cases hp:s.Nonempty; swap; · unfold MS.Tide.fare; rw [Finset.not_nonempty_iff_eq_empty.mp hp,zeroZ hB'.1,zeroZ Xc.1]; change PeakT.twin l P mildG (higher P _ * 0) 0; rw [mul_zero]; exact PeakT.twin0
     obtain ⟨ ht',hf',hu' ⟩:= hX' s hp n
     have hΩ: toZ D s n=toZ U' s n:= by
       funext i; let g(t:ℝ):= (D s n) i (exp t) []; have he : (fun t:ℝ=> U' s n i t [])=g:= funext fun t=> by rw [ hUe, τv ]
       obtain Ht:= ((hDQ s hp n).1 i).comp tendsto_exp_atTop; obtain HH:=ht'.1 i; change Tendsto (fun t:ℝ=> U' s n i t [] ) _ _ at HH; rw [ he ] at HH; exact tendsto_nhds_unique Ht HH
     obtain hh:= shapeO hu u0.reality ( marketV ht' hf' hu' ); refine ⟨ Verdict.economic _ _ (hX'' s hp n|>.2.1.2.2),?_⟩; rw [← ht ]; unfold MS.Tide.fare; rw [ hΩ, ← mul_sub ]; exact significant hh
 -- now estimates; no linking of the two rate terms
 have hd(s:Finset W)(n:ℕ): Vol l P L ( MS.Tide.fare h P f s n - MS.Tide.fare h P ( toZ D ) s n ):= by
    by_cases hp : s.Nonempty; swap; · unfold MS.Tide.fare; rw [ Finset.not_nonempty_iff_eq_empty.mp hp, h0,zeroZ Xc.1,sub_self ]; exact Vol.zero
    unfold MS.Tide.fare; rw [← mul_sub]; apply Vol.high; exact (paid_out (hpay s hp n|>.2)).restrict ((Filter.EventuallyEq.rfl).sub (HS n s))
 have hD(s:Finset W)(n:ℕ): Vol l P L ( MS.Tide.fare h P z s n - MS.Tide.fare h P ( toZ D ) s n ):= by
    by_cases hp : s.Nonempty; swap; · unfold MS.Tide.fare; rw [ Finset.not_nonempty_iff_eq_empty.mp hp, he,zeroZ Xc.1,sub_self ]; exact Vol.zero
    unfold MS.Tide.fare; rw [← mul_sub]; exact Vol.high (paid_out (hpr s hp n|>.2)) _
 have hA(s:Finset W)(n:ℕ): Tight l P L ( MS.Tide.fare h P f s n ) ( toZ B' s n ):= ⟨ (hm s n).1, by convert (hd s n).covers.plus (Total.alt (hm s n|>.2)) using 1; abel ⟩
 refine ⟨ f,z,fun i s=>⟨hU i s, σPay co i hz hX.badge⟩, fun i s=> (?_),⟨ h0,he⟩,⟨ X,U,D,E,B',hI,hZ,hf,hz,⟨ hUX,hXU,hDQ,hEQ ⟩,hB',fun s hs n=>⟨ hX'' s hs n |>.2.1,(hpay s hs n).1,(hpr s hs n).1,(hpay s hs n).2,(hpr s hs n).2⟩, fun n s=>⟨ HS n s, hm s n ⟩ ⟩, fun s n=>⟨ ?_, ?_, ?_⟩ ⟩
 · exact ( Top.identifies Y u A ( κ i ) _ ( dimT L i ) _ s ( ⟨ ( L i ).val,two_mul (α:=ℕ) _ ⟩ ) ).mp (hU i s)
 · rw [← show toZ B' s n=(fun i=>book S u μ (testP T i) s n) from funext fun _=> Point_t S u μ (posed co u0.knit) hB' _ s n ]; exact hA s n
 · rw [← show ordZ ( toZ B' ) s n=(fun i=>tour S u μ (testP T i) s n) from funext fun i=> shape_f S u μ ( posed co u0.knit ) hB' i s n, ← funext (fun i=> PeakT.ν_norm h (s:=s) ( n:=n ) ( «P»:=P ) i f ) ]; exact Tier.push _ _ hA s n
 convert (hd s n).sub ( hD s n ) using 1; abel
end YM.FVA2.Removal
