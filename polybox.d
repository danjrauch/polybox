import std.stdio;
import std.algorithm;
import std.math;
import std.file;
import std.string;
import std.format;
import std.range;
import std.datetime.stopwatch : benchmark, StopWatch, AutoStart;

static immutable EPS = real.epsilon;

struct point
{
public:
    real x, y;
    bool opEquals()(auto const ref point other) const
    {
        return fabs(x - other.x) < EPS && (fabs(y - other.y) < EPS);
    }

    int opCmp(const ref point other) const
    {
        if (fabs(x - other.x) < EPS && fabs(y - other.y) < EPS)
            return 0;
        if (fabs(x - other.x) > EPS && x < other.x)
            return -1;
        //if (fabs(y - other.y) > EPS && y < other.y)
        //    return -1;
        return 1;
    }

    point opBinary(string op)(const point rhs)
    {
        static if (op == "+")
            return point(x + rhs.x, y + rhs.y);
        else static if (op == "-")
            return point(x - rhs.x, y - rhs.y);
        else
            static assert(0, "Operator " ~ op ~ " not implemented");
    }

    point opBinary(string op)(const real rhs)
    {
        static if (op == "*")
            return point(x * rhs, y * rhs);
        else static if (op == "/")
            return point(x / rhs, y / rhs);
        else
            static assert(0, "Operator " ~ op ~ " not implemented");
    }

    point opBinaryRight(string op)(const real lhs)
    {
        static if (op == "*")
            return point(x * lhs, y * lhs);
        else
            static assert(0, "Operator " ~ op ~ " not implemented");
    }

    void toString(void delegate(const(char)[]) sink) const
    {
        sink.formattedWrite!"(%s, %s)"(x, y);
    }

    //string toString() const 
    //{
    //    return format("(%s,%s)", x, y);
    //}
}

pure real dist(const point p, const point q)
{
    return hypot(p.x - q.x, p.y - q.y);
}

unittest
{
    auto p = point(0, 0);
    auto q = point(1, 1);
    assert(dist(p, q) == sqrt(2.0));
}

pure real cross(const point p, const point q, const point r)
{
    return (q.x - p.x) * (r.y - p.y) - (r.x - p.x) * (q.y - p.y);
}

pure bool ccw(const point p, const point q, const point r)
{
    return cross(p, q, r) > 0;
}

pure bool colinear(const point p, const point q, const point r)
{
    return fabs(cross(p, q, r)) < EPS;
}

unittest
{
    auto p = point(1, 0);
    auto q = point(0, 1);
    auto r = point(-1, 0);
    assert(ccw(p, q, r));
    assert(!ccw(r,q,p));
}

struct polygon
{
private:
    point[] vxs;

public:
    this(point[] points)
    {
        vxs = points;
        this.sort();
    }

    bool opEquals()(auto const ref polygon other) const
    {
        if (vxs.length != other.vxs.length)
        {
            return false;
        }
        foreach (i, v; vxs)
        {
            if (v != other.vxs[i])
            {
                return false;
            }
        }
        return true;
    }

    inout(point) opIndex(size_t index) inout
    {
        return vxs[index];
    }

    point[] opIndex(size_t[2] r)
    {
        return vxs[r[0] .. r[1]];
    }

    point[] opIndex()
    {
        return vxs[];
    }

    size_t[2] opSlice(size_t dim)(size_t start, size_t end)
    in
    {
        assert(start >= 0 && end <= this.length);
    }
    body
    {
        return [start, end];
    }

    ref polygon opOpAssign(string op)(point value)
    {
        if (op == "~")
        {
            vxs ~= value;
        }
        return this;
    }

    @property size_t length() const
    {
        return vxs.length;
    }

    @property size_t opDollar() const
    {
        return vxs.length;
    }

    void toString(void delegate(const(char)[]) sink) const
    {
        sink.formattedWrite!("[\n");
        foreach(v; vxs)
        {
            sink.formattedWrite!("\t%s\n")(v);
        }
        sink.formattedWrite!("]");
    }

    //string toString() const
    //{
    //    return format("[\n%s\n]", join(vxs.map!(p => "\t" ~ p.toString()), "\n"));
    //}

    void sort()
    {
        real x = 0;
        real y = 0;
        foreach (p; vxs)
        {
            x += p.x;
            y += p.y;
        }
        point center = point(x / this.length, y / this.length);
        auto less = (point p, point q) {
            if (p.x - center.x >= 0 && q.x - center.x < 0)
            {
                return true;
            }
            if (p.x - center.x < 0 && q.x - center.x >= 0)
            {
                return false;
            }
            if (p.x - center.x == 0 && q.x - center.x == 0)
            {
                if (p.y - center.y >= 0 || q.y - center.y >= 0)
                {
                    return p.y > q.y;
                }
                return q.y > p.y;
            }
            auto det = cross(center, p, q);
            if (det < 0)
            {
                return true;
            }
            if (det > 0)
            {
                return false;
            }
            real d1 = (p.x - center.x) * (p.x - center.x) + 
                (p.y - center.y) * (p.y - center.y);
            real d2 = (q.x - center.x) * (q.x - center.x) + 
                (q.y - center.y) * (q.y - center.y);
            return d1 > d2;
        };
        std.algorithm.sort!(less)(vxs);
    }
}

unittest
{
    polygon P = polygon([
            point(1, 1), point(-1, -1), point(1, -1), point(-1, 1)
            ]);
    polygon Q = polygon([
            point(1, -1), point(-1, 1), point(1, 1), point(-1, -1)
            ]);
    assert(P == Q);
}

bool is_convex(polygon P)
{
    if (P.length <= 2)
    {
        return false;
    }
    immutable turnRight = !ccw(P[0], P[1], P[2]);
    foreach (i, p; P[1 .. $ - 2])
    {
        if (ccw(p, P[i + 1], P[i + 2]) == turnRight)
        {
            return false;
        }
    }
    if (P[0] != P[$ - 1])
    {
        if (ccw(P[$ - 2], P[$ - 1], P[0]) == turnRight)
        {
            return false;
        }
    }
    return true;
}

unittest
{
    if (exists("testdata/convex_hull.out"))
    {
        File file = File("testdata/convex_hull.out", "r");
        polygon P;
        while (!file.eof())
        {
            point p;
            string line = strip(file.readln());
            uint nitems = formattedRead(line, " %s %s", &p.x, &p.y);
            if (nitems == 2)
            {
                P ~= p;
            }
        }
        P.sort();
        assert(is_convex(P));
    }
}

polygon convex_hull(const point[] points)
{
    auto _points = points.dup;
    if (_points.length <= 3)
    {
        return polygon(_points);
    }
    sort(_points);
    auto compute_hull = (bool is_upper) {
        auto hull = [_points[0], _points[1]];
        if (!is_upper)
        {
            hull[0].y = -hull[0].y;
            hull[1].y = -hull[1].y;
        }
        foreach (p; _points[2 .. $])
        {
            p.y = is_upper ? p.y : -p.y;
            while (hull.length >= 2 && !ccw(p, hull[$ - 1], hull[$ - 2]))
            {
                hull.popBack();
            }
            hull ~= p;
        }
        if (!is_upper)
        {
            hull.each!((ref p) => p.y = -p.y);
        }
        return hull;
    };
    return polygon(compute_hull(true) ~ compute_hull(false)[1 .. $ - 1]);
}

unittest
{
    if (exists("testdata/convex_hull.in") && exists("testdata/convex_hull.out"))
    {
        File file = File("testdata/convex_hull.in", "r");
        point[] space;
        while (!file.eof())
        {
            point p;
            string line = strip(file.readln());
            uint nitems = formattedRead(line, " %s %s", &p.x, &p.y);
            if (nitems == 2)
            {
                space ~= p;
            }
        }
        file.close();
        file = File("testdata/convex_hull.out", "r");
        point[] ans_points;
        while (!file.eof())
        {
            point p;
            string line = strip(file.readln());
            uint nitems = formattedRead(line, " %s %s", &p.x, &p.y);
            if (nitems == 2)
            {
                ans_points ~= p;
            }
        }
        polygon A = polygon(ans_points);
        polygon P = convex_hull(space);
        assert(P == A);
    }
}

void main()
{
    auto sw = StopWatch(AutoStart.no);
    auto a = point(0, 1);
    auto b = point(1, 0);
    auto c = point(-1, 0);
    auto d = point(0, -1);
    auto e = point(0, 0);
    sw.start();
    writeln(convex_hull([a, b, c, d, e]));
    sw.stop();
    writeln("Runtime: ", sw.peek.total!"nsecs", " ns");
}

// dub run dfmt -- --inplace --max_line_length=80 geometry.d
