import YM.SignedWilsonExpansion.Contrast.Flint
-- Variable field motion purchases (on full LP later)
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.SignedWilsonExpansion.Carbon.Sierra
open FVA2 Register FVA2.Arrival Scale Scale.Jury MS MS.Menus MS.High MS.Local.Physical MS.Native MS.Land MS.Fleet
open MeasureTheory Function Filter Set XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1 Asymptotics PowerSeries Maxwell Maxwell.Free
open WickFace ProbeB Contrast Belle Belle.Path Belle.Buffet WilsonCoeffUV.Mer.Xa MarqueQ Crops Scale.Level Scale.Equator Scale.Facets
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} (N: WilsonPrescription G){q: Bool}{Y:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{S:Prescription (Press.portDeck G)}{h:G.Simple}(H: Main.Match N h Y S q)
local notation "W"=> ( Measure.start N.scheme N.criterion 4 )
local notation "Z"=> N.scheme
local notation "ψ"=> N.criterion
local notation "Q'"=> H.details.toServed.toPosted.toQuoted.toContract.toMission.born
variable (i:Fin 3)(x: Scale.Stage 3)
local notation "θ"=> Sec G 4
local notation "Φ"=> Extent.token
local notation "Y¹"=> Tags G 4 3
local notation "Ξ"=> leaf G 4
open Future Dancer Dancer.SeatsW PorchK Flint Commission
section
variable {ι:Type}{L:Filter ι}{τ t:ι→ℝ}{x y: ι→ Points 3}{f g p s:ι→ PowerSeries ℂ}
local notation "ξ"=> (1:ι→ℝ)
-- prepares Bounded+Convergence second moments including any masked proper faces.N.B.Basket differs (PS→actual).
structure Roam (L:Filter ι)(f g:ι→ PowerSeries ℂ):Prop where
     left (b:ℕ): charge b L ξ ξ f
     right (b:ℕ): charge b L ξ ξ g
     meet (b:ℕ): (fun i=> coeff b (f i)- coeff b (g i))=o[L] ξ
variable (v: Roam L f g)(u:Roam L p s)
include v u
lemma Roam.boost : Roam L (f+p) (g+s):=by
    have h {f g:ι→ PowerSeries ℂ} (b:ℕ)(p:charge b L ξ ξ f)(q:charge b L ξ ξ g): charge b L ξ ξ (f+g):=by intro i u; simp_rw [Pi.add_apply,map_add]; exact Wage.plus awarded ( p i u ) ( q i u )
    refine ⟨fun i=> h i (v.left i) (u.left i), fun i=> h i (v.right i) (u.right i), fun i=>?_⟩; refine ( ( v.meet i ).add ( u.meet i ) ).congr_left (fun j=> ?_ ); simp only [Pi.add_apply,map_add]; ring
omit u in
lemma Roam.negated : Roam L (-f) (-g):= by
    have h {f:ι→ PowerSeries ℂ}(b:ℕ)(p:charge b L ξ ξ f): charge b L ξ ξ (-f):=by intro i w; simp_rw [Pi.neg_apply,map_neg]; exact Wage.neg (p i w)
    refine ⟨ fun _=> h _ (v.left _),fun _=> h _ (v.right _),fun i=>?_⟩; simp only [Pi.neg_apply,map_neg,neg_sub_neg]; exact ( v.meet i ).neg_left.congr_left (fun i=> by ring)
lemma Roam.grow : Roam L (f*p) (g*s):=by
    have h {f p:ι→PowerSeries ℂ} (b:ℕ)(v:charge b L ξ ξ f)(u:charge b L ξ ξ p): charge b L ξ ξ (f*p):=by simpa only [show (fun i=> f i * p i)=f*p from rfl,one_mul] using charge.mul (t0:=ξ) awarded v u
    refine ⟨fun b=>h b (v.left b) (u.left b),fun b=>h b (v.right b) (u.right b), fun b=>?_ ⟩; simp_rw [Pi.mul_apply,PowerSeries.coeff_mul,← Finset.sum_sub_distrib]; apply IsLittleO.sum; intro i _; exact muCash ( unfoldW ( u.left i.2 i.2 le_rfl ) ) ( unfoldW ( v.right i.1 i.1 le_rfl ) ) ( u.meet i.2 ) ( v.meet i.1 ) -- neg alpha
omit u v in
lemma turn (a d:Rose.Badge→ι→ PowerSeries ℂ)(v:∀ m,Roam L (a m) ( d m )): Roam L ( fun i=> Rose.b3 fun m=> a m i ) (fun i=> Rose.b3 fun m=> d m i ) :=by
    let p:= Roam.boost (v Finset.univ) (Roam.negated (Roam.boost (Roam.boost ( Roam.grow (v {0,1}) (v {2}) ) ( Roam.grow (v {0,2}) ( v {1} ) )) ( Roam.grow (v {1,2}) ( v {0} ) )))
    let t:= Roam.grow (Roam.grow (v {0}) (v {1})) ( v {2} ); refine Eq.mp (?_) ( Roam.boost p ( Roam.boost t t ) ); congr 1 <;> ( ext1 i; simp only [ Pi.mul_apply,Pi.add_apply,Pi.neg_apply,two_smul,Rose.b3,sub_eq_add_neg ] )
omit u v
variable {U:Set (Points 3)} (w:Roi U) (hz:∀ᶠ i in L,x i∈ U) {A:ι→ Tags G 4 3} (hv:∀ j:Fin 3,By ℂ L (fun i=> A i j ) (lens G))
include H w hz hv
open Scale.Level
lemma moving (m:Rose.Badge) : Roam L (fun i=> typist W m (A i) (x i)) (fun i=> typist W m (testE G 3) (x i)) :=by
    let X(i):= Rose.missing (A i) m; let Y' := maskE G m
    have hp (j:Fin 3): By ℂ L (fun i=> X i j) (Y' j):=by
         by_cases he:j∈m <;> simp only [ X,Y',Rose.missing,maskE,testE,he,↓reduceIte ] <;> first| exact hv j | exact SeatsW.constant _
    have he (k:ℕ)(y:Tags G 4 3): (fun i=> Jury.fxt W (x i) k y)=O[L] ξ := (Path.cost (L:=L) _ _ H.details.toServed.toPosted.toQuoted h w _ _).comp_tendsto (tendsto_id.prodMk (tendsto_principal.mpr hz))
    have hu (t:ℕ): (fun i=> Jury.fxt W (x i) t (X i))=O[L] ξ:= matIncome ( he t ) (fun i=> income (hp i) )
    refine ⟨ fun _ k _=> ?_, fun _ k _=>?_, fun i=>?_ ⟩; · simp_rw [ typist, coeff_mk ]; exact Wage.enroll ( hu k )
    · simp_rw [typist,coeff_mk]; exact Wage.enroll ( he k _ )
    simp_rw [typist,coeff_mk]; refine matPays (v:=fun i:ι=>Y') (p:=X) ( he i ) (fun i=> income (SeatsW.constant (Y' i) )) (fun i=> income (hp i)) ( fun j (t: Module.Dual ℂ θ)=>?_ ); simp_rw [map_sub]; apply (isLittleO_one_iff ℝ).mpr; convert (hp j t).sub_const (t (Y' j)) using 2; rw[sub_self]
local notation "ν"=> ( coeff 2 )
local notation "u0"=> testE G 3
variable (z:Roam L f g)
lemma duo : Roam L (fun i=> compiled W (A i) (x i)) (fun i=>compiled W (testE G 3) (x i)):= turn (fun m i=> typist W m (A i) (x i)) _ (fun m=> moving N H w hz hv m)
open Scale Level
variable (l: IsEquivalent L τ t)(T: Tendsto τ L (𝓝 0))(b:ℕ)(wb:2≤b)
local notation "M0"=> ( t^2 )
variable (a:ι→Rose.Badge→ℂ)
abbrev copies (b:ℕ)(x:ι→Points 3)(t τ:ι→ℝ)(A:ι→ Tags G 4 3)(a:ι→Rose.Badge→ℂ) : Prop:= ∀ m:Rose.Badge,( fun i=> a i m- mote W b (x i) (τ i) ( Rose.missing (A i) m ))=o[L](t^2)
include l T wb
variable (P:copies (L:=L) N b x t τ A a)
lemma milestone (M:copies (L:=L) N b x t τ A a) : (fun i=> cumul (a i)- calcT (τ i) 2 ( compiled W (A i) (x i) ))=o[L] M0:=by
    let τ'(i):= (τ i:ℂ); have p:∀ᶠ i in L,|τ i|≤1:= T.norm.eventually_le_const (by simp: ‖(0:ℝ)‖<1); have u': b+1>2:= lt_of_le_of_lt wb ( Nat.lt_succ_self _ )
    let f'(m:Rose.Badge)(i:ι):= typist W m (A i) (x i)
    have hB(m:Rose.Badge): Basket L b τ M0 (f' m) (fun i=> a i m):=by
         have w':=( moving N H w hz hv m ).left b; have he: (fun i=> a i m- calcT (τ i) b (f' m i))=o[L] M0 := ( M m ).congr_left (fun i=>?_ ); swap; · rw[timed]; unfold f' typist Path.mote; simp_rw [coeff_mk]; exact congr_arg (a i m - ·) ( Finset.sum_congr rfl fun j _=> mul_comm .. )
         refine ⟨ w',inCash he ( Basket.earns p w' ) ( (( Wipe.stop ( l.tendsto_nhds T ) ).pow 2).congr_right (fun i=> one_pow _) ), he ⟩ -- find p args
    have hx:= scheme f' (fun m i=> a i m) hB p ( Wipe.expense T l u' ); let f(i:ι):= compiled W (A i) (x i); have hZ: (fun i=> calcT (τ' i) b (f i)-calcT (τ' i) 2 (f i))=o[L] M0:=by
          have HT:= unfoldW ( clockQ.dropFee awarded p τ' ( Wipe.earth_p ( isBigO_refl .. ) ) f hx.purse 2 b wb le_rfl ); simp only [one_mul] at HT; exact HT.trans_isLittleO ( Wipe.expense T l ( by norm_num ) )
    exact (hx.cost.add hZ).congr_left fun i=> sub_add_sub_cancel ..
variable {V:Set (Points 3)} (hv':Roi V)(u1:∀ᶠ i in L,y i∈V)(d:ι→ Rose.Badge→ ℂ)(c:x =ᶠ[L] ((2:ℝ)⁻¹ • y))(cor:∀ᶠ i in L,y i=(2:ℝ) • x i)(ν₀:ℝ)
include ν₀ hv' u1 cor
lemma loud (M:copies (L:=L) N b x t τ A a)(B:copies (L:=L) N b y t τ A d) : (fun i=> ( cumul ( a i )-(2:ℂ)^12*cumul (d i) ) - receipt W 2 (x i) * ( t i : ℂ )^2 )=o[L] M0 :=by
    let g(i):= (τ i:ℂ)^2; let p(i):=(t i:ℂ)^2; let κ₀:ℂ:= (2:ℂ)^12; let V(z:ι→Points 3)(v:ι→ Y¹)(i:ι):= compiled W (v i) (z i); let v(z:ι→Points 3)(i:ι):= ν ( V z A i ); let w'(z:ι→Points 3)(i:ι):= criterion W 2 (z i)
    have he:(fun i=>g i - p i )=o[L] M0:=by
        have h:(fun i=> ( τ i ^2-t i^2 ))=o[L] M0:= l.pow 2; exact ( Wipe.guise h ).congr_left fun i=> by unfold g p; rw[ Complex.ofReal_sub,Complex.ofReal_pow,Complex.ofReal_pow ]
    have wg:g=O[L] M0:= ( Wipe.earth_p (l.pow 2|>.isBigO) ).congr_left fun i=> ( Complex.ofReal_pow .. )
    have fu(z:ι→Points 3)(s: Roam L (V z A) (V z (fun _=>u0))) : (fun i=>v z i*g i-w' z i*p i)=o[L]M0:=by
       let x':=s.meet 2; have hz': (fun i=> (v z i-w' z i)*g i)=o[L] M0:= ( x'.mul_isBigO wg ).congr_right (fun i=> one_mul _ ); have hπ: (fun i=> w' z i*(g i-p i))=o[L] M0 := (( unfoldW ( s.right 2 2 le_rfl ) ).mul_isLittleO he).congr_right (fun i=> one_mul _ ); exact ( hz'.add hπ ).congr_left fun i=> by ring
    let hQ:= milestone N H w hz hv l T b wb a M; let hP:= milestone N H hv' u1 hv l T b wb d B; refine ( (hQ.add (fu x ( duo N H w hz hv )) ).sub ( ( hP.add (fu y (duo N H hv' u1 hv )) ).const_mul_left κ₀ ) ).congr' (?_) ( .refl .. ); filter_upwards [cor,hz] with i hv hi; let x': Scale.Stage 3:= ⟨x i,w.2 hi⟩; let y':= Scale.Facets.posing (-Real.log 2) x'; have ya: y'.val=y i:= ( ProbeB.twice x' ).trans hv.symm
    have hs:κ₀*coeff 0 ( V y A i )= coeff 0 ( V x A i ):= by obtain hg:=Flint.tide N H x' ν₀ (-Real.log 2) ( A i ); rw [ ProbeB.measure_t,ya ] at hg; exact hg
    have hV(z:ι→Points 3)(x:Scale.Stage 3)(px:x.val=z i): calcT (τ i) 2 (V z A i)=coeff 0 ( V z A i )+v z i * g i:=by
         have hu: coeff 1 ( V z A i )=0:=by dsimp only [V]; rw[←px]; exact snow N H _ ν₀ ( A i )
         rw [timed]; simp only[ Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,hu,zero_mul,add_zero,zero_add,mul_one ]; rfl
    change cumul _- calcT _ _ ( V x A i ) + (_ - w' x i * p i) - κ₀* ( cumul ( d i )- calcT _ _ (V y A i)+(v y i*g i-w' y i*p i))=_; rw [hV x x' rfl,hV y y' ya, ← hs ]; rw[ show receipt W 2 (x i)= w' x i-κ₀*w' y i from by unfold receipt; rw  [← hv] ]; change _ = cumul _- κ₀*cumul _- _ * p i; ring
end
end YM.SignedWilsonExpansion.Carbon.Sierra
