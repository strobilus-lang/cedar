/*
 * Copyright Cedar Contributors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use smol_str::SmolStr;
use std::collections::HashSet;

use crate::ast::{BinaryOp, ExprKind, Expr, Literal, ExprShapeOnly};
use crate::ast::EntityType;


/// A set of capabilities. Used to represent knowledge about attribute existence
/// before and after evaluating an expression.
#[derive(Eq, PartialEq, Debug, Clone, Default)]
pub struct CapabilitySet<'a>(HashSet<Capability<'a>>);

impl<'a> CapabilitySet<'a> {
    /// An empty capability set
    pub fn new() -> Self {
        CapabilitySet(HashSet::new())
    }

    /// A capability set with a single [`Capability`]
    pub fn singleton(e: Capability<'a>) -> Self {
        let mut set = Self::new();
        set.0.insert(e);
        set
    }

    /// Construct the union of `self` and `other`
    pub fn union(&self, other: &Self) -> Self {
        CapabilitySet(self.0.union(&other.0).cloned().collect())
    }

    /// Construct the intersection of `self` and `other`
    pub fn intersect(&self, other: &Self) -> Self {
        CapabilitySet(self.0.intersection(&other.0).cloned().collect())
    }

    /// Does this capability set contain the given [`Capability`]
    pub fn contains(&self, e: &Capability<'_>) -> bool {
        self.0.contains(e)
    }

    /// filtp(α) — remove capabilities involving the `in` operator
    /// Used by: AddParent, RemoveParent
    pub fn filtp(&self) -> Self {
        CapabilitySet(
            self.0
                .iter()
                .filter(|cap| !Self::expr_contains_in(cap.on_expr.0.as_ref()))
                .cloned()
                .collect()
        )
    }

    /// filta(f, α) — removes capabilities whose expression accesses attribute `f`
    /// Used by: UpdateAttribute, RemoveAttribute
    pub fn filta(&self, f: &str) -> Self {
        CapabilitySet(
            self.0
                .iter()
                .filter(|cap| !Self::expr_references_attribute(cap.on_expr.as_expr(), f))
                .cloned()
                .collect()
        )
    }

    /// filtt(E, α) — removes capabilities that reference entities of type E
    /// Used by: UpdateEntity, RemoveEntity
    pub fn filtt(&self, entity_type: &EntityType) -> Self {
        CapabilitySet(
            self.0
                .iter()
                .filter(|cap| {
                    !Self::expr_references_entity_type(cap.on_expr.0.as_ref(), entity_type)
                })
                .cloned()
                .collect()
        )
    }



    /// Returns true if `f` appears as an accessed attribute anywhere in `expr`.
    /// Used by filta
    fn expr_references_attribute(expr: &Expr, f: &str) -> bool {
        match expr.expr_kind() {
            // base cases: the attribute f is accessed or tested here
            ExprKind::GetAttr { expr, attr } | ExprKind::HasAttr { expr, attr } => {
                attr.as_str() == f || Self::expr_references_attribute(expr, f)
            }

            // recursive cases: inspect every sub-expression
            ExprKind::If { test_expr, then_expr, else_expr } => {
                Self::expr_references_attribute(test_expr, f)
                    || Self::expr_references_attribute(then_expr, f)
                    || Self::expr_references_attribute(else_expr, f)
            }
            ExprKind::And { left, right } | ExprKind::Or { left, right } => {
                Self::expr_references_attribute(left, f)
                    || Self::expr_references_attribute(right, f)
            }
            ExprKind::UnaryApp { arg, .. } => Self::expr_references_attribute(arg, f),
            ExprKind::BinaryApp { arg1, arg2, .. } => {
                Self::expr_references_attribute(arg1, f)
                    || Self::expr_references_attribute(arg2, f)
            }
            ExprKind::ExtensionFunctionApp { args, .. } => {
                args.iter().any(|a| Self::expr_references_attribute(a, f))
            }
            ExprKind::Like { expr, .. } | ExprKind::Is { expr, .. } => {
                Self::expr_references_attribute(expr, f)
            }
            ExprKind::Set(elements) => {
                elements.iter().any(|e| Self::expr_references_attribute(e, f))
            }
            ExprKind::Record(fields) => {
                fields.values().any(|e| Self::expr_references_attribute(e, f))
            }

            // leaf expressions cannot reference an attribute
            ExprKind::Lit(_)
            | ExprKind::Var(_)
            | ExprKind::Slot(_)
            | ExprKind::Unknown(_) => false,

            #[cfg(feature = "tolerant-ast")]
            ExprKind::Error { .. } => false,
        }
    }

    /// Returns true if the `in` operator appears anywhere in `expr`.
    /// Used by filtp
    fn expr_contains_in(expr: &Expr) -> bool {
        match expr.expr_kind() {
            // base case: the `in` operator is found
            ExprKind::BinaryApp { op: BinaryOp::In, arg1, arg2 } => {
                true || Self::expr_contains_in(arg1) || Self::expr_contains_in(arg2)
            }

            // recursive cases: inspect every sub-expression
            ExprKind::If { test_expr, then_expr, else_expr } => {
                Self::expr_contains_in(test_expr)
                    || Self::expr_contains_in(then_expr)
                    || Self::expr_contains_in(else_expr)
            }
            ExprKind::And { left, right } | ExprKind::Or { left, right } => {
                Self::expr_contains_in(left) || Self::expr_contains_in(right)
            }
            ExprKind::UnaryApp { arg, .. } => Self::expr_contains_in(arg),
            ExprKind::BinaryApp { arg1, arg2, .. } => {
                Self::expr_contains_in(arg1) || Self::expr_contains_in(arg2)
            }
            ExprKind::ExtensionFunctionApp { args, .. } => {
                args.iter().any(|a| Self::expr_contains_in(a))
            }
            ExprKind::GetAttr { expr, .. }
            | ExprKind::HasAttr { expr, .. }
            | ExprKind::Like { expr, .. }
            | ExprKind::Is { expr, .. } => Self::expr_contains_in(expr),
            ExprKind::Set(elements) => {
                elements.iter().any(|e| Self::expr_contains_in(e))
            }
            ExprKind::Record(fields) => {
                fields.values().any(|e| Self::expr_contains_in(e))
            }

            // leaf expressions cannot contain the `in` operator
            ExprKind::Lit(_)
            | ExprKind::Var(_)
            | ExprKind::Slot(_)
            | ExprKind::Unknown(_) => false,

            #[cfg(feature = "tolerant-ast")]
            ExprKind::Error { .. } => false,
        }
    }

    /// Returns true if an entity of type `entity_type` is referenced anywhere in `expr`.
    /// Used by filtt
    fn expr_references_entity_type(expr: &Expr, entity_type: &EntityType) -> bool {
        match expr.expr_kind() {
            // base case: an entity literal of the given type
            ExprKind::Lit(Literal::EntityUID(uid)) => uid.entity_type() == entity_type,

            // recursive cases: inspect every sub-expression
            ExprKind::If { test_expr, then_expr, else_expr } => {
                Self::expr_references_entity_type(test_expr, entity_type)
                    || Self::expr_references_entity_type(then_expr, entity_type)
                    || Self::expr_references_entity_type(else_expr, entity_type)
            }
            ExprKind::And { left, right } | ExprKind::Or { left, right } => {
                Self::expr_references_entity_type(left, entity_type)
                    || Self::expr_references_entity_type(right, entity_type)
            }
            ExprKind::UnaryApp { arg, .. } => {
                Self::expr_references_entity_type(arg, entity_type)
            }
            ExprKind::BinaryApp { arg1, arg2, .. } => {
                Self::expr_references_entity_type(arg1, entity_type)
                    || Self::expr_references_entity_type(arg2, entity_type)
            }
            ExprKind::ExtensionFunctionApp { args, .. } => {
                args.iter().any(|a| Self::expr_references_entity_type(a, entity_type))
            }
            ExprKind::GetAttr { expr, .. }
            | ExprKind::HasAttr { expr, .. }
            | ExprKind::Like { expr, .. }
            | ExprKind::Is { expr, .. } => {
                Self::expr_references_entity_type(expr, entity_type)
            }
            ExprKind::Set(elements) => {
                elements.iter().any(|e| Self::expr_references_entity_type(e, entity_type))
            }
            ExprKind::Record(fields) => {
                fields.values().any(|e| Self::expr_references_entity_type(e, entity_type))
            }

            // other leaf expressions do not reference an entity type
            ExprKind::Lit(_)
            | ExprKind::Var(_)
            | ExprKind::Slot(_)
            | ExprKind::Unknown(_) => false,

            #[cfg(feature = "tolerant-ast")]
            ExprKind::Error { .. } => false,
        }
    }
    
    /// Removes every capability whose attribute is exactly `f`, regardless of
    /// its expression. Implements the set difference α ∖ {(e', f) | e' ∈ Expr}.
    pub fn remove_attribute_caps(&self, f: &str) -> Self {
        let f_expr = Expr::val(SmolStr::new(f));
        CapabilitySet(
            self.0
                .iter()
                .filter(|cap| cap.attribute_or_tag.as_expr() != &f_expr)
                .cloned()
                .collect()
        )
    } 
}

/// Represent a single capability, which is an expression and some attribute that is
/// known to exist for that expression.
#[derive(Hash, Eq, PartialEq, Debug, Clone)]
pub struct Capability<'a> {
    /// For this expression
    on_expr: ExprShapeOnly<'a, ()>,
    /// This attribute or tag is known to exist on that expression
    ///
    /// This expression represents the attribute or tag name. It should have type string.
    /// Often this is a string constant, but in the case of tags it can be an expression.
    attribute_or_tag: ExprShapeOnly<'a, ()>,
    /// Is `attribute_or_tag` an attribute name or a tag name
    kind: CapabilityKind,
}

#[derive(Hash, Eq, PartialEq, Debug, Clone, Copy)]
enum CapabilityKind {
    /// This capability is for accessing attributes
    Attribute,
    /// This capability is for accessing tags
    Tag,
}

impl<'a> Capability<'a> {
    /// Construct a new [`Capability`] stating that the attribute `attribute` is
    /// known to exist for the expression `on_expr`
    pub fn new_attribute(on_expr: &'a Expr<()>, attribute: SmolStr) -> Self {
        Self {
            on_expr: ExprShapeOnly::new_from_borrowed(on_expr),
            attribute_or_tag: ExprShapeOnly::new_from_owned(Expr::val(attribute)),
            kind: CapabilityKind::Attribute,
        }
    }

    /// Construct a new [`Capability`] stating that the tag `tag` is
    /// known to exist for the expression `on_expr`
    pub fn new_borrowed_tag(on_expr: &'a Expr<()>, tag: &'a Expr<()>) -> Self {
        Self {
            on_expr: ExprShapeOnly::new_from_borrowed(on_expr),
            attribute_or_tag: ExprShapeOnly::new_from_borrowed(tag),
            kind: CapabilityKind::Tag,
        }
    }

    /// Construct a new [`Capability`] stating that the tag `tag` is
    /// known to exist for the expression `on_expr`
    pub fn new_owned_tag(on_expr: &'a Expr<()>, tag: Expr<()>) -> Self {
        Self {
            on_expr: ExprShapeOnly::new_from_borrowed(on_expr),
            attribute_or_tag: ExprShapeOnly::new_from_owned(tag),
            kind: CapabilityKind::Tag,
        }
    }
}
