"""Portable structured review output for agents and controlled evaluations."""
from . import report as rr

def schema_object(**fields):
    return {"type": "object", "properties": fields, "required": list(fields), "additionalProperties": False}


def schema_array(item, **limits):
    return {"type": "array", "items": item, **limits}


def schema_enum(*values):
    return {"type": "string", "enum": list(values)}


STRING = {"type": "string"}


BOOLEAN = {"type": "boolean"}


def review_schema(request, max_calls=30, context=()):
    paths = [item["path"] for item in request.get("sources", [])]
    paths += [f"evidence/tool-{n:03d}.json" for n in range(1, max_calls + 1)]
    evidence = schema_array(schema_enum(*paths, *context), minItems=1)
    return schema_object(
        request_id=schema_enum(request["id"]),
        reviewer=STRING,
        context_policy=schema_enum("fresh", "rereview"),
        prior_reviews=schema_array(STRING),
        coverage=schema_object(**{angle: schema_enum("complete", "incomplete") for angle in rr.ANGLES}),
        findings=schema_array(
            schema_object(
                angle=schema_enum(*rr.ANGLES),
                file=schema_enum(*request["scope"]),
                line={"type": "integer", "minimum": 0},
                severity=schema_enum("semantic", "nit"),
                message=STRING,
                suggestion=STRING,
                evidence=evidence,
            )
        ),
        questions=schema_array(STRING),
        reconciliations=schema_array(
            schema_object(
                prior_evidence=schema_enum(*context) if context else STRING,
                status=schema_enum("retained", "corrected", "withdrawn"),
                reason=STRING,
                evidence=evidence,
            ),
            **({} if context else {"maxItems": 0}),
        ),
    )
